import Proof.NormalVelocitySecondError
import Proof.CurveAffineError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

/-- The actual vertical Jacobi position has its quadratic connection correction,
    with an error uniformly quadratic in the initial speed. -/
theorem NormalCoordinates.position_variation_second_error {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v u : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(normalVelocityVariation expMap y v u t).1-t • u+t^2 • connection g y v u‖ ≤
      normalVelocitySecondErrorBudget K C D*‖v‖^2*‖u‖*t^2 := by
  let B := normalVelocitySecondErrorBudget K C D*‖v‖^2*‖u‖
  let c := connection g y v u
  let W : ℝ → X := fun s => (normalVelocityVariation expMap y v u s).2+(2*s) • c
  have hB : 0 ≤ B := by dsimp [B,normalVelocitySecondErrorBudget,normalVariationErrorBudget];positivity
  have hWD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt W (deriv (fun q => (normalVelocityVariation expMap y v u q).2) s+(2:ℝ) • c) s := by
    have hVel := hasDerivAt_prod_snd (hN.hasDerivAt_phase_variation hΩ hg hK hy v u hv hs)
    have hScale : HasDerivAt (fun q : ℝ => (2*q) • c) ((2:ℝ) • c) s := by
      convert ((hasDerivAt_id s).const_mul 2).smul_const c using 1 <;> simp
    exact hVel.differentiableAt.hasDerivAt.add hScale
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hWError (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖W s-u‖ ≤ B*s := by
    have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun q hq => (hWD q hq).differentiableAt)
      (fun q hq => by
        rw [(hWD q hq).deriv]
        exact hN.velocity_variation_acceleration_second_error hΩ hg hK hC hD hΓ0 hΓ1 hy v u hv hv1 hq) hz hs
    have hZero : W 0 = u := by
      simp only [W,c,normalVelocityVariation,hN.phase_variation_zero hy v u hv,mul_zero,zero_smul,add_zero]
    rw [hZero] at hb
    simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg hs.1] using hb
  let F : ℝ → X := fun s => (normalVelocityVariation expMap y v u s).1+s^2 • c
  have hFD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt F (W s) s := by
    have hScale : HasDerivAt (fun q : ℝ => q^2 • c) ((2*s) • c) s := by
      convert ((hasDerivAt_id s).pow 2).smul_const c using 1 <;> simp
    exact (hN.hasDerivAt_variation_position hΩ hg hK hy v u hv hs).add hScale
  have hFZero : F 0 = 0 := by
    simp only [F,normalVelocityVariation,hN.phase_variation_zero hy v u hv,zero_pow (by norm_num : 2≠0),zero_smul,add_zero]
  have hb := norm_curve_affine_error_le F W 0 u B t hB ht hFD hFZero hWError
  have hEq : (normalVelocityVariation expMap y v u t).1-t • u+t^2 • connection g y v u = F t-0-t • u := by
    dsimp [F,c];abel
  rw [hEq]
  exact hb

end ShrinkingSpheres
