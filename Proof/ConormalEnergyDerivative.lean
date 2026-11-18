import Proof.CompositionTaylorDerivative
import Proof.EnergyConormalTaylorBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments

/-- The actual fixed testing map and probability-sphere Riesz normalization
    preserve the quadratic derivative scale of the energy/Poisson product. -/
theorem norm_conormal_energy_taylor_derivative_le
    {T H : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E E1 : T → H →L[ℝ] H →L[ℝ] ℝ) (E0 : H →L[ℝ] H →L[ℝ] ℝ)
    (P P1 : T → SphereSobolev (1/2:ℝ) →L[ℝ] H)
    (P0 : SphereSobolev (1/2:ℝ) →L[ℝ] H)
    (x : T) (r CA DA DB V1 D1 CS DS DQ : ℝ)
    (hE : DifferentiableAt ℝ E x) (hE1 : DifferentiableAt ℝ E1 x)
    (hP : DifferentiableAt ℝ P x) (hP1 : DifferentiableAt ℝ P1 x)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCA : 0 ≤ CA) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hV1 : 0 ≤ V1) (hD1 : 0 ≤ D1) (hCS : 0 ≤ CS) (hDS : 0 ≤ DS) (hDQ : 0 ≤ DQ)
    (hNE : ‖E x‖ ≤ CA) (hDE : ‖fderiv ℝ E x‖ ≤ DA*r)
    (hDiffE : ‖E x-E0‖ ≤ DB*r)
    (hNP1 : ‖P1 x‖ ≤ V1) (hDP1 : ‖fderiv ℝ P1 x‖ ≤ D1)
    (hNPQ : ‖P x-P0-r • P1 x‖ ≤ CS*r^2)
    (hDPQ : ‖fderiv ℝ (fun p => P p-P0-r • P1 p) x‖ ≤ DS*r^2)
    (hDEQ : ‖fderiv ℝ (fun p => E p-E0-r • E1 p) x‖ ≤ DQ*r^2) :
    ‖fderiv ℝ (fun p => (sphereSobolevDualRieszL (1/2:ℝ)).comp
      (sphereSurfaceMass⁻¹ • ((E p).bilinearComp (P p) P0-E0.bilinearComp P0 P0-
        r • (E0.bilinearComp (P1 p) P0+(E1 p).bilinearComp P0 P0)))) x‖ ≤
      sphereSurfaceMass⁻¹*‖P0‖*(DA*CS+CA*DS+DA*V1+DB*D1+DQ*‖P0‖)*r^2 := by
  let R := fun p => (E p).comp (P p)-E0.comp P0-
    r • (E0.comp (P1 p)+(E1 p).comp P0)
  let Post : (H →L[ℝ] ℝ) →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) H ℝ).flip P0
  let Q := fun p => Post.comp (R p)
  have hR : DifferentiableAt ℝ R x := ((hE.clm_comp hP).sub_const (E0.comp P0)).sub
    ((((differentiableAt_const E0).clm_comp hP1).add (hE1.clm_comp (differentiableAt_const P0))).const_smul r)
  have hQ : DifferentiableAt ℝ Q x := (differentiableAt_const Post).clm_comp hR
  have hN := norm_composition_taylor_remainder_derivative_le E E1 E0 P P1 P0 x
    r CA DA DB V1 D1 CS DS DQ hE hE1 hP hP1 hr hr1
      hCA hDA hDB hV1 hD1 hCS hDS hDQ hNE hDE hDiffE hNP1 hDP1 hNPQ hDPQ hDEQ
  have hPost : ‖Post‖ ≤ ‖P0‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro ell
    exact (ContinuousLinearMap.opNorm_comp_le ell P0).trans_eq (mul_comm _ _)
  have hDRQ := norm_fderiv_clm_comp_le (fun _ : T => Post) R x (differentiableAt_const Post) hR
  simp only [fderiv_const_apply,norm_zero,zero_mul,zero_add] at hDRQ
  have hDQN : ‖fderiv ℝ Q x‖ ≤
      ‖P0‖*((DA*CS+CA*DS+DA*V1+DB*D1+DQ*‖P0‖)*r^2) :=
    hDRQ.trans (mul_le_mul hPost hN (norm_nonneg _) (norm_nonneg _))
  have hEq : (fun p => (E p).bilinearComp (P p) P0-E0.bilinearComp P0 P0-
        r • (E0.bilinearComp (P1 p) P0+(E1 p).bilinearComp P0 P0)) = Q := by
    funext p
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousLinearMap.ext
    intro g
    simp only [Q,Post,R,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]
  have hNormEq := congrArg (fun F : T → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) →L[ℝ] ℝ =>
    ‖fderiv ℝ (fun p => (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ • F p)) x‖) hEq
  refine hNormEq.le.trans ?_
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hDSQ : ‖fderiv ℝ (fun p => sphereSurfaceMass⁻¹ • Q p) x‖ ≤
      sphereSurfaceMass⁻¹*‖P0‖*(DA*CS+CA*DS+DA*V1+DB*D1+DQ*‖P0‖)*r^2 := by
    have hd := (hQ.hasFDerivAt.const_smul sphereSurfaceMass⁻¹).fderiv
    change fderiv ℝ (fun p => sphereSurfaceMass⁻¹ • Q p) x = _ at hd
    rw [hd,norm_smul,Real.norm_eq_abs,abs_of_nonneg hArea]
    exact (mul_le_mul_of_nonneg_left hDQN hArea).trans_eq (by ring)
  have hRiesz : ‖sphereSobolevDualRieszL (1/2:ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ell
    rw [norm_sphereSobolevDualRieszL_apply,one_mul]
  have hSQ : DifferentiableAt ℝ (fun p => sphereSurfaceMass⁻¹ • Q p) x :=
    hQ.const_smul (sphereSurfaceMass⁻¹)
  have hFinal := norm_fderiv_clm_comp_le (fun _ : T => sphereSobolevDualRieszL (1/2:ℝ))
    (fun p => sphereSurfaceMass⁻¹ • Q p) x (differentiableAt_const _) hSQ
  simp only [fderiv_const_apply,norm_zero,zero_mul,zero_add] at hFinal
  exact hFinal.trans ((mul_le_mul hRiesz hDSQ (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

end ShrinkingSpheres
