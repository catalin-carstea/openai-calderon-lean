module

public import Proof.CalderonN.NormalJacobiBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Port of the named module in the checked Proposition 5.3 release.
All variations refer to the admitted initial-velocity parameter of the same normal map. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

def normalVariationErrorBudget (K C D : ℝ) : ℝ :=
  Real.exp (1+2*C*K+D*K^2)*(2*C*K+D*K^2)

/-- The time derivative of the velocity variation gains a small initial-speed factor. -/
theorem NormalCoordinates.velocity_variation_acceleration_le {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun s : ℝ => (normalVelocityVariation expMap y v u s).2) t‖ ≤
      normalVariationErrorBudget K C D*‖v‖*‖u‖ := by
  let A : ℝ := 1+2*C*K+D*K^2
  let P := normalGeodesicPhase expMap y (v,t)
  let J := normalVelocityVariation expMap y v u t
  have hvd : v ∈ disk g y (R y) := interior_subset hv
  have hPos : P.1 ∈ Ω := hN.path_image hy v hvd ht
  have hSpeed : ‖P.2‖ ≤ K*‖v‖ := by
    rw [show P = (expMap (y,t • v),deriv (fun s : ℝ => expMap (y,s • v)) t) from hN.phase_eq hy v hvd ht]
    exact hN.geodesic_speed_le hΩ hg hK hy v hvd ht
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hExp : Real.exp (A*t) ≤ Real.exp A :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left ht.2 hA).trans_eq (mul_one A))
  have hJ : ‖J‖ ≤ ‖u‖*Real.exp A :=
    (hN.velocity_variation_bound hΩ hg hK hC hD hΓ0 hΓ1 hy v u hv hv1 ht).trans
      (mul_le_mul_of_nonneg_left hExp (norm_nonneg u))
  have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
  have hVar : HasDerivAt (fun s : ℝ => (normalVelocityVariation expMap y v u s).2)
      (fderiv ℝ (coordinateGeodesicSpray g) P J).2 t :=
    hasDerivAt_prod_snd (hN.hasDerivAt_phase_variation hΩ hg hK hy v u hv ht)
  rw [hVar.deriv]
  have hB := norm_fderiv_coordinateGeodesicSpray_snd_le g P J hdΓ C D (K*‖v‖)
    hC hD (mul_nonneg hK.le (norm_nonneg v)) (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
  have hCoeff : 0 ≤ 2*C*(K*‖v‖)+D*(K*‖v‖)^2 := by positivity
  have hFirst := hB.trans (mul_le_mul_of_nonneg_left hJ hCoeff)
  have hvSq : ‖v‖^2 ≤ ‖v‖ := by nlinarith [norm_nonneg v]
  have hSmall := mul_le_mul_of_nonneg_left hvSq (show 0 ≤ D*K^2 by positivity)
  have hSmall' := mul_le_mul_of_nonneg_right hSmall (show 0 ≤ ‖u‖*Real.exp A by positivity)
  change ‖(fderiv ℝ (coordinateGeodesicSpray g) P J).2‖ ≤ _
  unfold normalVariationErrorBudget
  change _ ≤ Real.exp A*(2*C*K+D*K^2)*‖v‖*‖u‖
  nlinarith only [hFirst,hSmall']

/-- Uniform error of the velocity component of the actual first variation. -/
theorem NormalCoordinates.velocity_variation_error_le {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(normalVelocityVariation expMap y v u t).2-u‖ ≤
      normalVariationErrorBudget K C D*‖v‖*‖u‖*t := by
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hasDerivAt_prod_snd (hN.hasDerivAt_phase_variation hΩ hg hK hy v u hv hs)).differentiableAt)
    (fun s hs => hN.velocity_variation_acceleration_le hΩ hg hK hC hD hΓ0 hΓ1 hy v u hv hv1 hs) hzero ht
  simpa only [normalVelocityVariation,hN.phase_variation_zero hy v u hv,
    sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using hb

/-- The position variation is close to its affine initial model. -/
theorem NormalCoordinates.position_variation_error_le {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(normalVelocityVariation expMap y v u t).1-t • u‖ ≤
      normalVariationErrorBudget K C D*‖v‖*‖u‖*t^2 := by
  let F : ℝ → (X dim) := fun s => (normalVelocityVariation expMap y v u s).1-s • u
  let B := normalVariationErrorBudget K C D*‖v‖*‖u‖
  have hB : 0 ≤ B := by unfold B normalVariationErrorBudget; positivity
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) 1 := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hFD (s : ℝ) (hs : s ∈ Icc (0:ℝ) t) :
      HasDerivAt F ((normalVelocityVariation expMap y v u s).2-u) s := by
    have hP := hN.hasDerivAt_variation_position hΩ hg hK hy v u hv (hsub hs)
    have hScale : HasDerivAt (fun q : ℝ => q • u) u s := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id s).smul_const u
    exact hP.sub hScale
  have hBound (s : ℝ) (hs : s ∈ Icc (0:ℝ) t) : ‖deriv F s‖ ≤ B*t := by
    rw [(hFD s hs).deriv]
    exact (hN.velocity_variation_error_le hΩ hg hK hC hD hΓ0 hΓ1 hy v u hv hv1 (hsub hs)).trans
      (mul_le_mul_of_nonneg_left hs.2 hB)
  have hz : (0:ℝ) ∈ Icc (0:ℝ) t := ⟨le_rfl,ht.1⟩
  have hl : t ∈ Icc (0:ℝ) t := ⟨ht.1,le_rfl⟩
  have hb := (convex_Icc (0:ℝ) t).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hFD s hs).differentiableAt) hBound hz hl
  simpa only [B,F,normalVelocityVariation,hN.phase_variation_zero hy v u hv,zero_smul,sub_zero,
    Real.norm_eq_abs,abs_of_nonneg ht.1,mul_assoc,← pow_two] using hb

end CalderonN
