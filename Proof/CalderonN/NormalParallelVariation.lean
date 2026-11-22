module

public import Proof.CalderonN.NormalJointVariationBounds
public import Proof.CalderonN.SeparatedSprayBounds
public import Proof.CalderonN.CurveAffineError

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalParallelVariation.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def normalParallelVariation (g : (MetricField dim)) (expMap : (X dim) × (X dim) → (X dim)) (y v a : (X dim)) (t : ℝ) : (X dim) × (X dim) :=
  normalJointVariation expMap y v a (-connection g y a v) t

@[expose] def parallelVariationBudget (K C D : ℝ) : ℝ := (1+C)*Real.exp (1+2*C*K+D*K^2)
@[expose] def parallelVelocityBudget (K C D : ℝ) : ℝ := C+(2*C*K+D*K^2)*parallelVariationBudget K C D
@[expose] def parallelAccelerationBudget (K C D : ℝ) : ℝ :=
  D*K^2*parallelVariationBudget K C D+2*C*K*parallelVelocityBudget K C D

variable {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v a : (X dim)) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)

include hΓ0 hN hy in
lemma NormalCoordinates.parallel_initial_velocity_bound :
    ‖-connection g y a v‖ ≤ C*‖a‖*‖v‖ := by
  rw [norm_neg,← connectionBilinear_apply]
  exact (norm_bilinear_apply_le _ _ _).trans (by gcongr;exact hΓ0 y (hN.center_mem hy))

include hY hΩ hg hK hC hD hΓ0 hΓ1 hN hy hR hv hv1

/-- Parallel center variation has a common full phase bound. -/
theorem NormalCoordinates.parallel_variation_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖normalParallelVariation g expMap y v a t‖ ≤ parallelVariationBudget K C D*‖a‖ := by
  have hInitial : ‖((a,-connection g y a v):(X dim) × (X dim))‖ ≤ (1+C)*‖a‖ := by
    rw [Prod.norm_mk]
    apply max_le
    · nlinarith only [mul_nonneg hC (norm_nonneg a)]
    · have hb := (hN.parallel_initial_velocity_bound hΓ0 hy v a).trans
        (mul_le_mul_of_nonneg_left hv1 (mul_nonneg hC (norm_nonneg a)))
      nlinarith only [hb,norm_nonneg a]
  have hA : 0 ≤ 1+2*C*K+D*K^2 := by positivity
  have hExp : Real.exp ((1+2*C*K+D*K^2)*t) ≤ Real.exp (1+2*C*K+D*K^2) :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left ht.2 hA).trans_eq (mul_one _))
  have hb := hN.joint_variation_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a
    (-connection g y a v) hv hv1 ht
  exact hb.trans ((mul_le_mul hInitial hExp (Real.exp_pos _).le (by positivity)).trans_eq (by
    dsimp [parallelVariationBudget];ring))

lemma NormalCoordinates.parallel_acceleration_first_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun s => (normalParallelVariation g expMap y v a s).2) t‖ ≤
      ((2*C*K+D*K^2)*parallelVariationBudget K C D)*‖v‖*‖a‖ := by
  let P := normalJointPhase expMap ((y,v),t)
  let J := normalParallelVariation g expMap y v a t
  have hPos : P.1 ∈ Ω := hN.path_image hy v hv.le ht
  have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
  have hSpeed : ‖P.2‖ ≤ K*‖v‖ := by
    rw [show P = normalGeodesicPhase expMap y (v,t) from
      hN.jointPhase_eq_phase hy v t (smul_mem_disk_of_mem g y v (R y) t hv.le ht),hN.phase_eq hy v hv.le ht]
    exact hN.geodesic_speed_le hΩ hg hK hy v hv.le ht
  have hVar := hasDerivAt_prod_snd (hN.hasDerivAt_joint_variation hY hΩ hg hK hy hR v a
    (-connection g y a v) hv ht)
  change HasDerivAt (fun s => (normalParallelVariation g expMap y v a s).2)
    (fderiv ℝ (coordinateGeodesicSpray g) P J).2 t at hVar
  rw [hVar.deriv]
  have hJ := hN.parallel_variation_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a hv hv1 ht
  have hB := norm_fderiv_coordinateGeodesicSpray_snd_le g P J hdΓ C D (K*‖v‖)
    hC hD (by positivity) (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
  have hCoeff : 0 ≤ 2*C*(K*‖v‖)+D*(K*‖v‖)^2 := by positivity
  have hFirst := hB.trans (mul_le_mul_of_nonneg_left hJ hCoeff)
  have hvSq : ‖v‖^2 ≤ ‖v‖ := by nlinarith [norm_nonneg v]
  have hSmall := mul_le_mul_of_nonneg_left hvSq
    (show 0 ≤ D*K^2*(parallelVariationBudget K C D*‖a‖) by
      unfold parallelVariationBudget;positivity)
  change ‖(fderiv ℝ (coordinateGeodesicSpray g) P J).2‖ ≤ _
  nlinarith only [hFirst,hSmall]

/-- The velocity of a parallel center variation retains one initial-speed factor. -/
theorem NormalCoordinates.parallel_velocity_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖(normalParallelVariation g expMap y v a t).2‖ ≤ parallelVelocityBudget K C D*‖v‖*‖a‖ := by
  have hZero := hN.joint_variation_zero hY hΩ hg hy hR v a (-connection g y a v) hv
  change normalParallelVariation g expMap y v a 0 = (a,-connection g y a v) at hZero
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hasDerivAt_prod_snd (hN.hasDerivAt_joint_variation hY hΩ hg hK hy hR v a
      (-connection g y a v) hv hs)).differentiableAt)
    (fun s hs => hN.parallel_acceleration_first_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a hv hv1 hs) hz ht
  have hSub : ‖(normalParallelVariation g expMap y v a t).2-(-connection g y a v)‖ ≤
      ((2*C*K+D*K^2)*parallelVariationBudget K C D)*‖v‖*‖a‖ := by
    have hBB : 0 ≤ ((2*C*K+D*K^2)*parallelVariationBudget K C D)*‖v‖*‖a‖ := by
      unfold parallelVariationBudget;positivity
    have hh : ‖(normalParallelVariation g expMap y v a t).2-(-connection g y a v)‖ ≤
        (((2*C*K+D*K^2)*parallelVariationBudget K C D)*‖v‖*‖a‖)*t := by
      change ‖(normalParallelVariation g expMap y v a t).2-
        (normalParallelVariation g expMap y v a 0).2‖ ≤
          (((2*C*K+D*K^2)*parallelVariationBudget K C D)*‖v‖*‖a‖)*‖t-0‖ at hb
      rw [hZero] at hb
      simpa only [sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using hb
    exact hh.trans ((mul_le_mul_of_nonneg_left ht.2 hBB).trans_eq (mul_one _))
  have hInitial := hN.parallel_initial_velocity_bound hΓ0 hy v a
  calc
    _ = ‖((normalParallelVariation g expMap y v a t).2-(-connection g y a v))+(-connection g y a v)‖ := by rw [sub_add_cancel]
    _ ≤ ‖(normalParallelVariation g expMap y v a t).2-(-connection g y a v)‖+‖-connection g y a v‖ := norm_add_le _ _
    _ ≤ ((2*C*K+D*K^2)*parallelVariationBudget K C D)*‖v‖*‖a‖+C*‖a‖*‖v‖ := add_le_add hSub hInitial
    _ = _ := by dsimp [parallelVelocityBudget];ring

/-- The parallel center variation acceleration is quadratic in the initial speed. -/
theorem NormalCoordinates.parallel_acceleration_second_bound {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun s => (normalParallelVariation g expMap y v a s).2) t‖ ≤
      parallelAccelerationBudget K C D*‖v‖^2*‖a‖ := by
  let P := normalJointPhase expMap ((y,v),t)
  let J := normalParallelVariation g expMap y v a t
  have hPos : P.1 ∈ Ω := hN.path_image hy v hv.le ht
  have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
  have hSpeed : ‖P.2‖ ≤ K*‖v‖ := by
    rw [show P = normalGeodesicPhase expMap y (v,t) from
      hN.jointPhase_eq_phase hy v t (smul_mem_disk_of_mem g y v (R y) t hv.le ht),hN.phase_eq hy v hv.le ht]
    exact hN.geodesic_speed_le hΩ hg hK hy v hv.le ht
  have hVar := hasDerivAt_prod_snd (hN.hasDerivAt_joint_variation hY hΩ hg hK hy hR v a
    (-connection g y a v) hv ht)
  change HasDerivAt (fun s => (normalParallelVariation g expMap y v a s).2)
    (fderiv ℝ (coordinateGeodesicSpray g) P J).2 t at hVar
  rw [hVar.deriv]
  have hPosBound := (norm_fst_le J).trans
    (hN.parallel_variation_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a hv hv1 ht)
  have hVelBound := hN.parallel_velocity_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a hv hv1 ht
  have hB := norm_fderiv_spray_snd_separated g P J hdΓ C D (K*‖v‖)
    hC hD (by positivity) (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeed
  exact hB.trans ((add_le_add
    (mul_le_mul_of_nonneg_left hPosBound (by positivity))
    (mul_le_mul_of_nonneg_left hVelBound (by positivity))).trans_eq (by
      dsimp [parallelAccelerationBudget];ring))

end CalderonN
