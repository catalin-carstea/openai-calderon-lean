import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace ShrinkingSpheres

/-- The genuine first Poisson correction is a fixed linear image of its
    first coefficient energy family, so its derivative uses no inverse derivative. -/
theorem fixed_first_poisson_energy_derivative
    {P Z E F H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : Z →L[ℝ] E) (I : F →L[ℝ] Z) (H0 : H →L[ℝ] E)
    (T1 : P → E →L[ℝ] F) (x : P) (hT1 : DifferentiableAt ℝ T1 x)
    (C0 D1 : ℝ) (hC0 : 0 ≤ C0) (hD1 : 0 ≤ D1)
    (hJ : ‖J‖ ≤ 1) (hI : ‖I‖ ≤ C0) (hDT1 : ‖fderiv ℝ T1 x‖ ≤ D1) :
    DifferentiableAt ℝ (fun p => -(J.comp (I.comp ((T1 p).comp H0)))) x ∧
      ‖fderiv ℝ (fun p => -(J.comp (I.comp ((T1 p).comp H0)))) x‖ ≤ C0*D1*‖H0‖ := by
  let Post := -(J.comp I)
  have hId : (fun p => -(J.comp (I.comp ((T1 p).comp H0)))) =
      fun p => Post.comp ((T1 p).comp H0) := by
    funext p
    simp only [Post,ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_assoc]
  have hInner : DifferentiableAt ℝ (fun p => (T1 p).comp H0) x :=
    hT1.clm_comp (differentiableAt_const H0)
  have hDiff : DifferentiableAt ℝ (fun p => Post.comp ((T1 p).comp H0)) x :=
    (differentiableAt_const Post).clm_comp hInner
  have hNormPost : ‖Post‖ ≤ C0 := by
    change ‖-(J.comp I)‖ ≤ C0
    rw [norm_neg]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hJ hI (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hPre := norm_fderiv_clm_comp_le T1 (fun _ : P => H0) x hT1 (differentiableAt_const H0)
  have hPost := norm_fderiv_clm_comp_le (fun _ : P => Post)
    (fun p => (T1 p).comp H0) x (differentiableAt_const Post) hInner
  simp only [fderiv_const_apply,norm_zero,zero_mul,mul_zero,zero_add,add_zero] at hPre hPost
  have hPreN : ‖fderiv ℝ (fun p => (T1 p).comp H0) x‖ ≤ D1*‖H0‖ :=
    hPre.trans (mul_le_mul_of_nonneg_right hDT1 (norm_nonneg H0))
  have hBound : ‖fderiv ℝ (fun p => Post.comp ((T1 p).comp H0)) x‖ ≤ C0*D1*‖H0‖ :=
    hPost.trans ((mul_le_mul hNormPost hPreN (norm_nonneg _) hC0).trans_eq (by ring))
  constructor
  · exact hId.symm ▸ hDiff
  · exact (congrArg (fun f : P → H →L[ℝ] E => ‖fderiv ℝ f x‖) hId).le.trans hBound

end ShrinkingSpheres
