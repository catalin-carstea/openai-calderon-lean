import Proof.NormalSecondVariationError
import Proof.NormalJacobianSecondDerivative
import Proof.CurveAffineError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

/-- The second initial-velocity position variation is -t^2 Gamma to an error
    that vanishes linearly in the initial speed. -/
theorem NormalCoordinates.second_velocity_position_error {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D E : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v u k : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(secondParameterVariation (normalGeodesicPhase expMap y) u k (v,t)).1+
      t^2 • connectionBilinear g y k u‖ ≤ secondVelocityPrincipalErrorBudget K C D E*‖v‖*‖u‖*‖k‖*t^2 := by
  let Z : ℝ → X × X := fun s => secondParameterVariation (normalGeodesicPhase expMap y) u k (v,s)
  let c := connectionBilinear g y k u
  let B := secondVelocityPrincipalErrorBudget K C D E*‖v‖*‖u‖*‖k‖
  let W : ℝ → X := fun s => (Z s).2+(2*s) • c
  have hB : 0 ≤ B := by
    dsimp [B,secondVelocityPrincipalErrorBudget,secondNormalVariationBudget,normalVariationErrorBudget];positivity
  have hWD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt W (deriv (fun q => (Z q).2) s+(2:ℝ) • c) s := by
    have hVel := hasDerivAt_prod_snd (hN.hasDerivAt_second_phase_variation hΩ hg hK hy v u k hv hs)
    have hScale : HasDerivAt (fun q : ℝ => (2*q) • c) ((2:ℝ) • c) s := by
      convert ((hasDerivAt_id s).const_mul 2).smul_const c using 1 <;> simp
    exact hVel.differentiableAt.hasDerivAt.add hScale
  have hZero : Z 0 = 0 := hN.second_phase_variation_zero hy v u k hv
  have hWZero : W 0 = 0 := by simp only [W,hZero,mul_zero,zero_smul,add_zero,Prod.snd_zero]
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hWError (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖W s-0‖ ≤ B*s := by
    have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun q hq => (hWD q hq).differentiableAt)
      (fun q hq => by
        rw [(hWD q hq).deriv]
        exact hN.second_velocity_acceleration_error hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy v u k hv hv1 hq) hz hs
    rw [hWZero] at hb
    simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg hs.1] using hb
  have hPosition (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt (fun q => (Z q).1) (Z s).2 s := by
    let P := normalGeodesicPhase expMap y (v,s)
    let Ju := firstParameterVariation (normalGeodesicPhase expMap y) u (v,s)
    let Jk := firstParameterVariation (normalGeodesicPhase expMap y) k (v,s)
    have hPos : P.1 ∈ Ω := hN.path_image hy v (interior_subset hv) hs
    have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    have hLin : (fderiv ℝ (coordinateGeodesicSpray g) P (Z s)).1 = (Z s).2 := by
      rw [fderiv_coordinateGeodesicSpray g P hdΓ (Z s).1 (Z s).2]
    have hForce : (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) P Jk Ju).1 = 0 := by
      rw [hg.second_fderiv_coordinateGeodesicSpray hΩ hK P hPos Ju.1 Ju.2 Jk.1 Jk.2]
    have hVal : (fderiv ℝ (coordinateGeodesicSpray g) P (Z s)+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) P Jk Ju).1 = (Z s).2 := by
      change (fderiv ℝ (coordinateGeodesicSpray g) P (Z s)).1+
        (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) P Jk Ju).1 = _
      rw [hLin,hForce,add_zero]
    exact (hasDerivAt_prod_fst (hN.hasDerivAt_second_phase_variation hΩ hg hK hy v u k hv hs)).congr_deriv hVal
  let F : ℝ → X := fun s => (Z s).1+s^2 • c
  have hFD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt F (W s) s := by
    have hScale : HasDerivAt (fun q : ℝ => q^2 • c) ((2*s) • c) s := by
      convert ((hasDerivAt_id s).pow 2).smul_const c using 1 <;> simp
    exact (hPosition s hs).add hScale
  have hFZero : F 0 = 0 := by simp only [F,hZero,zero_pow (by norm_num : 2≠0),zero_smul,add_zero,Prod.fst_zero]
  have hb := norm_curve_affine_error_le F W 0 0 B t hB ht hFD hFZero hWError
  simpa only [sub_zero,smul_zero,F,Z,c] using hb

/-- The genuine second vertical endpoint derivative has its zero-radius value
    -Gamma plus a speed-linear operator error. -/
theorem NormalCoordinates.normalVerticalJacobian_derivative_error {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D E : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (normalVerticalJacobian expMap y) v+connectionBilinear g y‖ ≤
      secondVelocityPrincipalErrorBudget K C D E*‖v‖ := by
  have hB : 0 ≤ secondVelocityPrincipalErrorBudget K C D E := by
    dsimp [secondVelocityPrincipalErrorBudget,secondNormalVariationBudget,normalVariationErrorBudget];positivity
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hB (norm_nonneg v))
  intro k u
  have hb := hN.second_velocity_position_error hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy v u k hv hv1
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  simp only [one_pow,one_smul,mul_one] at hb
  rw [hN.second_variation_position_eq hy v u k hv] at hb
  exact hb.trans_eq (by ring)

end ShrinkingSpheres
