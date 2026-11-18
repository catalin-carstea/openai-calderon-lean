import Proof.NormalParallelVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

variable {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v a : X) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)

include hY hΩ hg hK hC hD hΓ0 hΓ1 hN hy hR hv hv1

/-- The parallel center variation has the expected affine initial model with
    a uniformly quadratic error. -/
theorem NormalCoordinates.parallel_position_affine_error {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(normalParallelVariation g expMap y v a t).1-a-t • (-connection g y a v)‖ ≤
      parallelAccelerationBudget K C D*‖v‖^2*‖a‖*t^2 := by
  let B := parallelAccelerationBudget K C D*‖v‖^2*‖a‖
  have hB : 0 ≤ B := by
    dsimp [B,parallelAccelerationBudget,parallelVelocityBudget,parallelVariationBudget];positivity
  have hZero := hN.joint_variation_zero hY hΩ hg hy hR v a (-connection g y a v) hv
  change normalParallelVariation g expMap y v a 0 = (a,-connection g y a v) at hZero
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hVel (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖(normalParallelVariation g expMap y v a s).2-(-connection g y a v)‖ ≤ B*s := by
    have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun q hq => (hasDerivAt_prod_snd (hN.hasDerivAt_joint_variation hY hΩ hg hK hy hR v a
        (-connection g y a v) hv hq)).differentiableAt)
      (fun q hq => hN.parallel_acceleration_second_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a hv hv1 hq) hz hs
    change ‖(normalParallelVariation g expMap y v a s).2-
      (normalParallelVariation g expMap y v a 0).2‖ ≤ B*‖s-0‖ at hb
    rw [hZero] at hb
    simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg hs.1] using hb
  have hPosition (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun q => (normalParallelVariation g expMap y v a q).1)
        (normalParallelVariation g expMap y v a s).2 s := by
    let P := normalJointPhase expMap ((y,v),s)
    let J := normalParallelVariation g expMap y v a s
    have hPos : P.1 ∈ Ω := hN.path_image hy v hv.le hs
    have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    have he := congrArg Prod.fst (fderiv_coordinateGeodesicSpray g P hdΓ J.1 J.2)
    have hVal : (fderiv ℝ (coordinateGeodesicSpray g) P J).1 = J.2 := by simpa only [Prod.eta] using he
    exact (hasDerivAt_prod_fst (hN.hasDerivAt_joint_variation hY hΩ hg hK hy hR v a
      (-connection g y a v) hv hs)).congr_deriv hVal
  apply norm_curve_affine_error_le _ _ a (-connection g y a v) B t hB ht hPosition _ hVel
  exact congrArg Prod.fst hZero

end ShrinkingSpheres
