module

public import Proof.CalderonN.ConformalCylinderAgreement

import Proof.CalderonN.EndpointTaylor
import Proof.CalderonN.DilationJetBounds
import Proof.CalderonN.MetricCalculus
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-! Adapted from `CylinderTransferTaylor` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2200000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] {normal : I dim}

/-- Positive lower bound for the actual chart density on the compact
cylinder, uniform in the small dilation. -/
theorem exists_uniform_conformalCylinder_volumeFloor
    {g : (MetricField dim)} (hg : SmoothMetric univ g) :
    ∃ m : ℝ, 0 < m ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ y ∈ interior (coordinateCylinder normal), m ≤ chartVolume (conformalReference (depthScale normal 4) g lam) y := by
  let γ (q : ℝ × (X dim)) := conformalReference (depthScale normal 4) g q.1 q.2
  let K := Icc (0 : ℝ) 1 ×ˢ (coordinateCylinder normal)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_coordinateCylinder (normal := normal))
  have hG (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => γ q i j) univ := by
    have hDepth := (contDiff_depthScale (normal := normal) 4).comp
      (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × (X dim) → (X dim)))
    have hmet := (contDiffOn_univ.mp (hg.1 i j)).comp
      (contDiff_fst.smul contDiff_snd : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => q.1 • q.2))
    exact (hDepth.mul hmet).contDiffOn
  have hpos (q : ℝ × (X dim)) : 0 < (γ q).det :=
    ((hg.2 _ (mem_univ _)).smul (depthScale_pos (normal := normal) 4 q.2)).det_pos
  have hvol : ContinuousOn (fun q : ℝ × (X dim) => Real.sqrt (γ q).det) K :=
    (((contDiffOn_det_of_entries hG).sqrt (fun q _ => (hpos q).ne')).mono
      (subset_univ K)).continuousOn
  obtain ⟨m,hm,hbound⟩ := hK.exists_forall_le' hvol (a := (0 : ℝ)) (fun q _ =>
    Real.sqrt_pos.mpr (hpos q))
  refine ⟨m,hm,?_⟩
  have hI : ∀ᶠ lam in 𝓝 (0 : ℝ), lam < 1 := Iio_mem_nhds zero_lt_one
  exact hI.mono fun lam hl hpos y hy =>
    hbound (lam,y) ⟨⟨hpos.le,hl.le⟩,interior_subset hy⟩

set_option maxHeartbeats 580000 in
/-- The radius-squared Taylor remainder for the finite family follows
from the prepared normal coordinates and the original smooth chart
functions. The bound is uniform before the dilation and sphere level. -/
theorem exists_uniform_conformalCylinder_pair_remainder
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) (h₀ : (0 : (X dim)) ∈ Ω)
    {n : ℕ} {u : Fin n → (X dim) → ℝ} (hu : ∀ a, ContDiffOn ℝ ∞ (u a) Ω)
    {g₁ g₂ : (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {p : ℕ} {R ε K ρ c₀ floor : ℝ} {m : ℕ} {Mv : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hK : 0 < K) (hρ : 0 ≤ ρ)
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor Mv Cj) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∀ A : (TraceAdjoint dim), ∀ a y, y ∈ interior (coordinateCylinder normal) → ∀ w : ↥(standardSphere dim),
        let d := conformalSphereData normal g₁ g₂ E p R lam δ A
        let v := renormalizedHarmonic (u a 0) (fderiv ℝ (u a) 0) (u a) lam
        let z := endpoint d.expMap d.radius (y,frameVector d.frame y w)
        |v z - (v y + fderiv ℝ v y (z-y))| ≤ C * (d.radius y)^2 := by
  let Y := interior (coordinateCylinder normal)
  let O := ball (0 : (X dim)) 3
  let D := closedBall (0 : (X dim)) 3
  have hYO : Y ⊆ O := interior_subset.trans ((coordinateCylinder_subset_closedBall (normal := normal)).trans
    (closedBall_subset_ball (by norm_num)))
  let γ (lam : ℝ) := conformalReference (depthScale normal 4) g₁ lam
  let c (a : Fin n) := u a 0
  let B (a : Fin n) := fderiv ℝ (u a) 0
  obtain ⟨L,hL,hdisp⟩ := exists_uniform_normal_endpoint_displacement_of_speed (K := K) (R := ρ)
    (isCompact_coordinateCylinder (normal := normal)) (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hE hK.le hρ
  obtain ⟨M,hM,hJet⟩ := exists_uniform_renormalizedHarmonic_jet_bound hΩ h₀ (isCompact_closedBall (0 : (X dim)) 3)
    hu c B (m := 2) (by omega)
  refine ⟨M*L^2,mul_nonneg (zero_le_one.trans hM) (sq_nonneg L),?_⟩
  apply (hSetup.and (hJet.and (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)))).mono
  intro lam hlam hl δ hδ A a y hy w
  let d := conformalSphereData normal g₁ g₂ E p R lam δ A
  let e := frameVector d.frame y w
  let z := endpoint d.expMap d.radius (y,e)
  let v := renormalizedHarmonic (c a) (B a) (u a) lam
  obtain ⟨hrad,hBack,hNormal,hProf⟩ := hlam.1 hl δ hδ A
  have hF : ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i = j then 1 else 0 :=
    hBack.2.2.2.2.2.2.2 y (hYO hy)
  have he : e ∈ sphereAt d.γ y := frameVector_mem_sphere d.γ d.frame y hF w
  have hr := hrad y hy
  have hsize : ‖e‖ ≤ Real.sqrt K := by
    have h := ((hBack.1.2 y (hYO hy)).2 e).1
    rw [show metricPair d.γ y e e = 1 from he,inv_mul_eq_div,div_le_iff₀ hK,one_mul] at h
    simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt h
  have hzero : E lam (y,0) = y := by
    have h := ((hNormal.2 y hy).2.2 0 (by simp [disk,metricPair,sq_nonneg])).2.2.1
    simpa only [zero_smul,conformalSphereData] using h
  have hzO : z ∈ O := by
    apply ((hNormal.2 y hy).2.2 (d.radius y • e) ?_).1
    change metricPair d.γ y (d.radius y • e) (d.radius y • e) ≤ ρ^2
    rw [metricPair_smul_same,show metricPair d.γ y e e = 1 from he,mul_one]
    exact pow_le_pow_left₀ hr.1.le hr.2.1.le 2
  have hz := hdisp lam ⟨hl.le,hlam.2.2.le⟩ y (interior_subset hy) (d.radius y)
    ⟨hr.1.le,hr.2.1.le⟩ e hsize hzero
  have hLine (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : y+t • (z-y) ∈ O := by
    have heq : y+t • (z-y) = (1-t) • y + t • z := by
      rw [smul_sub,sub_smul,one_smul]
      abel
    rw [heq]
    exact (convex_ball (0 : (X dim)) 3) (hYO hy) hzO (by linarith [ht.2]) ht.1 (by ring)
  have hRoom : IsOpen {z : (X dim) | lam • z ∈ Ω} :=
    hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)
  have hJ t (ht : t ∈ Icc (0 : ℝ) 1) :=
    hlam.2.1 hl (y+t • (z-y)) (ball_subset_closedBall (hLine t ht))
  apply abs_endpoint_affine_remainder_le v y z M L (d.radius y)
    (zero_le_one.trans hM) (mul_nonneg hL hr.1.le) hz
  · intro t ht
    exact ((contDiffOn_renormalizedHarmonic (hu a) (c a) (B a) lam).contDiffAt
      (hRoom.mem_nhds (hJ t ht).1)).of_le (by simp)
  · exact fun t ht => (hJ t ht).2 a

end CalderonN
