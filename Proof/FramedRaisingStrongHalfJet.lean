import Proof.FramedRaisingHalfCovariantData
import Proof.FramedRaisingSecondCovariantGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def framedRaisingFirstHalfJet (d : Data) (i b : I) (x : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ a : I,christoffel d.γ x a i b • framedRaisingHalfL d x (axis a)

lemma framedRaisingFirstHalfJet_coarse (d : Data) (i b : I) (x : X) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (framedRaisingFirstCoarseJet d i b x)=
      (framedRaisingFirstHalfJet d i b x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hR (a : I) := DFunLike.congr_fun (framedRaisingHalfL_coarse d x (axis a)) u
  simp only [ContinuousLinearMap.comp_apply] at hR
  simp only [framedRaisingFirstCoarseJet,framedRaisingFirstHalfJet,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul,hR]

/-- The first genuine covariant raising jet retains a bounded half-domain
extension, independently of derivatives of the orthonormal frame. -/
theorem uniform_framed_raising_strong_half_one_jet {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ,0 ≤ Q ∧ ∀ floor ε : ℝ,∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i b : I,
        ‖framedRaisingHalfL d y (axis b)‖ ≤ Q ∧ ‖framedRaisingFirstHalfJet d i b y‖ ≤ Q := by
  let M1 := |M ⟨1,by omega⟩|
  let G := 9*K*M1
  let Q0 := framedRaisingHalfBudget K (M 0) (M ⟨1,by omega⟩)
  let Q := Q0+3*G*Q0
  have hK0 := zero_le_one.trans hK
  have hQ0 : 0 ≤ Q0 := framedRaisingHalfBudget_nonneg _ _ _ hK0
  have hG : 0 ≤ G := by dsimp only [G,M1];positivity
  have hQ : 0 ≤ Q := by dsimp only [Q];positivity
  refine ⟨Q,hQ,?_⟩
  intro floor ε d hd y hy i b
  have hyΩ := hd.2.1.center_mem hy
  have hMetric (a c : I) : ‖fderiv ℝ (fun x => d.γ x a c) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound hm hyΩ a c).trans (le_abs_self _)
  have hGamma (a : I) : |christoffel d.γ y a i b| ≤ G :=
    hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) hyΩ M1 (abs_nonneg _) hMetric a i b
  have hRaise (a : I) : ‖framedRaisingHalfL d y (axis a)‖ ≤ Q0 :=
    ((hd.framedRaisingHalf_covariant_data hY hΩ hm hK a) y hy).1
  have hJet : ‖framedRaisingFirstHalfJet d i b y‖ ≤ 3*G*Q0 :=
    norm_weighted_sum_three_le _ _ _ _ hG hGamma hRaise
  refine ⟨(hRaise b).trans ?_,hJet.trans ?_⟩
  · exact le_add_of_nonneg_right (by positivity)
  · dsimp only [Q]
    linarith only [hQ0]

end ShrinkingSpheres
