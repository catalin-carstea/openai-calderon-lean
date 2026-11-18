import Proof.NormalFrameNormalizationParallelJet
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Function
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- The genuine open frame domain requires only a center in the admitted
metric region and an invertible raw frame. -/
def normalFramePositiveDomain (Ω : Set X) : Set NormalFrameParameter :=
  Prod.fst ⁻¹' Ω ∩ (fun p : NormalFrameParameter => p.2.2) ⁻¹' {L | IsUnit L}

lemma isOpen_normalFramePositiveDomain {Ω : Set X} (hΩ : IsOpen Ω) :
    IsOpen (normalFramePositiveDomain Ω) :=
  (hΩ.preimage continuous_fst).inter (Units.isOpen.preimage continuous_snd.snd)

lemma normalFramePositiveDomain_mem_of_orthonormal {Ω : Set X} (g : MetricField)
    (p : NormalFrameParameter) (hp : p.1 ∈ Ω)
    (he : ∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0) :
    p ∈ normalFramePositiveDomain Ω := by
  have hInj : Function.Injective p.2.2 := by
    intro u v huv
    have hZero : p.2.2 (u-v) = 0 := by rw [map_sub,huv,sub_self]
    have hPair := metricPair_orthonormal_linear g p he (u-v) (u-v)
    rw [hZero] at hPair
    have hz : inner ℝ (u-v) (u-v) = 0 := by simpa only [metricPair,PiLp.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero] using hPair.symm
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  refine ⟨hp,ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hInj,?_⟩⟩
  exact p.2.2.toLinearMap.surjective_of_injective hInj

lemma Elliptic.normalFramePositiveDomain_pair_positive {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {p : NormalFrameParameter} (hp : p ∈ normalFramePositiveDomain Ω)
    (u : X) (hu : u ≠ 0) : 0 < metricPair g p.1 (p.2.2 u) (p.2.2 u) := by
  have hInj : Function.Injective p.2.2 := (ContinuousLinearMap.isUnit_iff_bijective.mp hp.2).1
  have hLu : p.2.2 u ≠ 0 := by
    intro hh
    apply hu
    exact hInj (by simpa only [map_zero] using hh)
  exact (mul_pos (inv_pos.mpr hK) (sq_pos_of_pos (norm_pos_iff.mpr hLu))).trans_le ((h.2 p.1 hp.1).2 (p.2.2 u)).1

/-- A genuinely smooth orthonormal frame extension exists on an open domain
around every admitted orthonormal frame. All actual frame restrictions are
fixed exactly; no quantitative frame derivative assumption is introduced. -/
theorem Elliptic.normalFrame_normalization_open_domain {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) :
    IsOpen (normalFramePositiveDomain Ω) ∧
    ContDiffOn ℝ ∞ (normalizedOrthonormalFrameParameter g) (normalFramePositiveDomain Ω) ∧
    ∀ p ∈ normalFramePositiveDomain Ω,∀ i j,
      metricPair g p.1 (normalFrameNormalizedLinear g p (axis i)) (normalFrameNormalizedLinear g p (axis j)) =
        if i=j then 1 else 0 := by
  have hPos (p : NormalFrameParameter) (hp : p ∈ normalFramePositiveDomain Ω) :=
    h.normalFramePositiveDomain_pair_positive hK hp
  refine ⟨isOpen_normalFramePositiveDomain hΩ,?_,?_⟩
  · intro p hp
    exact (contDiffAt_normalizedOrthonormalFrameParameter g p
      (fun i j => (h.1 i j).contDiffAt (hΩ.mem_nhds hp.1)) (hPos p hp)).contDiffWithinAt
  · intro p hp
    exact normalFrameNormalizedLinear_orthonormal g p
      (fun u v => metricPair_symm g p.1 (p.2.2 u) (p.2.2 v) (h.2 p.1 hp.1).1) (hPos p hp)

end ShrinkingSpheres
