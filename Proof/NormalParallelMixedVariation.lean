import Proof.NormalJointSecondVariation
import Proof.NormalParallelVariation
import Proof.SprayMixedParallelBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

def mixedParallelForceBudget (K C D E : ℝ) : ℝ :=
  let P := parallelVariationBudget K C D
  let V := parallelVelocityBudget K C D
  let Q := Real.exp (1+2*C*K+D*K^2)
  2*C*Q*V+2*D*Q*K*V+2*D*P*Q*K+E*Q*P*K^2

def mixedParallelVariationBudget (K C D E : ℝ) : ℝ :=
  mixedParallelForceBudget K C D E*Real.exp (1+2*C*K+D*K^2)

/-- A parallel-center/velocity second variation gains one power of the initial
    speed. This is an estimate for the actual joint derivative of the normal map. -/
theorem NormalCoordinates.parallel_mixed_variation_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K C D E : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v a b : X) (hv : metricPair g y v v < (R y)^2)
    (hv1 : ‖v‖ ≤ 1) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖secondParameterVariation (normalJointPhase expMap) (a,-connection g y a v) (0,b) ((y,v),t)‖ ≤
      mixedParallelVariationBudget K C D E*‖v‖*‖a‖*‖b‖ := by
  let h : X × X := (a,-connection g y a v)
  let k : X × X := (0,b)
  let S : ℝ → X × X := fun s => secondParameterVariation (normalJointPhase expMap) h k ((y,v),s)
  let A : ℝ := 1+2*C*K+D*K^2
  let delta : ℝ := mixedParallelForceBudget K C D E*‖v‖*‖a‖*‖b‖
  let L : ℝ → (X × X) →L[ℝ] X × X :=
    fun s => fderiv ℝ (coordinateGeodesicSpray g) (normalJointPhase expMap ((y,v),s))
  let T : ℝ → X × X := fun s =>
    fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalJointPhase expMap ((y,v),s))
      (firstParameterVariation (normalJointPhase expMap) k ((y,v),s))
      (firstParameterVariation (normalJointPhase expMap) h ((y,v),s))
  have hA : 1 ≤ A := by
    have hh : 0 ≤ 2*C*K+D*K^2 := by positivity
    dsimp only [A]
    linarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hP : 0 ≤ parallelVariationBudget K C D := by unfold parallelVariationBudget;positivity
  have hV : 0 ≤ parallelVelocityBudget K C D := by unfold parallelVelocityBudget;positivity
  have hForce : 0 ≤ mixedParallelForceBudget K C D E := by
    unfold mixedParallelForceBudget;dsimp only;positivity
  have hDelta : 0 ≤ delta := by dsimp only [delta];positivity
  have hVar (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : HasDerivAt S (L s (S s)+T s) s :=
    hN.hasDerivAt_joint_second_variation hY hΩ hg hK hy hR v h k hv hs
  have hGeom (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      (normalJointPhase expMap ((y,v),s)).1 ∈ Ω ∧
        ‖(normalJointPhase expMap ((y,v),s)).2‖ ≤ K*‖v‖ := by
    refine ⟨hN.path_image hy v hv.le hs,?_⟩
    rw [hN.jointPhase_eq_phase hy v s (smul_mem_disk_of_mem g y v (R y) s hv.le hs),
      hN.phase_eq hy v hv.le hs]
    exact hN.geodesic_speed_le hΩ hg hK hy v hv.le hs
  have hLinear (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖L s‖ ≤ A := by
    obtain ⟨hPos,hSpeed⟩ := hGeom s hs
    have hdΓ := ((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    have hSpeedK := hSpeed.trans ((mul_le_mul_of_nonneg_left hv1 hK.le).trans_eq (mul_one K))
    exact norm_fderiv_coordinateGeodesicSpray_le g _ hdΓ C D K hC hD hK.le
      (hΓ0 _ hPos) (hΓ1 _ hPos) hSpeedK
  have hForcing (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖T s‖ ≤ delta := by
    obtain ⟨hPos,hSpeed⟩ := hGeom s hs
    have hJ : ‖firstParameterVariation (normalJointPhase expMap) h ((y,v),s)‖ ≤
        parallelVariationBudget K C D*‖a‖ :=
      hN.parallel_variation_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a hv hv1 hs
    have hJv : ‖(firstParameterVariation (normalJointPhase expMap) h ((y,v),s)).2‖ ≤
        parallelVelocityBudget K C D*‖v‖*‖a‖ :=
      hN.parallel_velocity_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a hv hv1 hs
    have hL : ‖firstParameterVariation (normalJointPhase expMap) k ((y,v),s)‖ ≤ Real.exp A*‖b‖ := by
      change ‖normalJointVariation expMap y v 0 b s‖ ≤ Real.exp A*‖b‖
      have hb := hN.joint_variation_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v 0 b hv hv1 hs
      have hExp : Real.exp (A*s) ≤ Real.exp A :=
        Real.exp_le_exp.mpr (mul_le_of_le_one_right hApos.le hs.2)
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg b),mul_comm] using
        hb.trans (mul_le_mul_of_nonneg_left hExp (norm_nonneg ((0,b):X × X)))
    exact hg.norm_second_spray_parallel_le hΩ hK (normalJointPhase expMap ((y,v),s))
      (firstParameterVariation (normalJointPhase expMap) h ((y,v),s))
      (firstParameterVariation (normalJointPhase expMap) k ((y,v),s)) hPos a b ‖v‖ C D E
      (parallelVariationBudget K C D) (parallelVelocityBudget K C D) (Real.exp A)
      (norm_nonneg v) hv1 hC hD hE hP hV (Real.exp_pos _).le
      (hΓ0 _ hPos) (hΓ1 _ hPos) (hΓ2 _ hPos) hSpeed hJ hJv hL
  have hCont : ContinuousOn S (Icc (0:ℝ) 1) := fun s hs => (hVar s hs).continuousAt.continuousWithinAt
  have hRight (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt S (L s (S s)+T s) (Ici s) s := (hVar s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt
  have hInitial : ‖S 0‖ ≤ 0 := by
    rw [show S 0 = 0 from hN.joint_second_variation_zero hY hΩ hg hy hR v h k hv,norm_zero]
  have hGrowth (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) : ‖L s (S s)+T s‖ ≤ A*‖S s‖+delta := by
    exact (norm_add_le _ _).trans (add_le_add
      (((L s).le_opNorm (S s)).trans (mul_le_mul_of_nonneg_right
        (hLinear s ⟨hs.1,hs.2.le⟩) (norm_nonneg (S s)))) (hForcing s ⟨hs.1,hs.2.le⟩))
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le hCont hRight hInitial hGrowth t ht
  simp only [gronwallBound_of_K_ne_0 hApos.ne',sub_zero,zero_mul,zero_add] at hb
  have hExp : Real.exp (A*t)-1 ≤ Real.exp A :=
    (sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr (mul_le_of_le_one_right hApos.le ht.2))
  have hDiv : delta/A ≤ delta := div_le_self hDelta hA
  have hFinal : ‖S t‖ ≤ delta*Real.exp A := hb.trans
    ((mul_le_mul_of_nonneg_left hExp (div_nonneg hDelta hApos.le)).trans
      (mul_le_mul_of_nonneg_right hDiv (Real.exp_pos A).le))
  exact hFinal.trans_eq (by dsimp only [delta,A,mixedParallelVariationBudget];ring)

end ShrinkingSpheres
