import Proof.RadialAdjointTaylorDerivative
import Proof.RadialAdjointTaylorPointControl
import Proof.FirstRadialAdjointCorrectionIdentity
import Proof.CommonSupportOneBoundaryTaylorDerivative
import Proof.CommonSupportRadialAdjointRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL

def radialAdjointDerivativeBudget (QA QD QJ QB : ℝ) : ℝ :=
  (73*36)*(QA+QD)+boundaryTangentialCoarseBudget*(78*QD)+
    boundaryTangentialAdjointBudget*((73*78)*QD)+QJ+QB

/-- A native, same-coefficient adjoint derivative estimate. All quantitative
    premises concern the actual coarse/H1 coefficient factors and the chosen
    forward response; genuine inverse neighborhoods are constructed here. -/
theorem commonSupport_radial_adjoint_taylor_derivative_le
    (A A1 : ℝ × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → A (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → A1 (t,z) = 0)
    (D : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (ell : ℝ → X →L[ℝ] ℝ)
    (hD : DifferentiableAt ℝ D 0) (hEll : DifferentiableAt ℝ ell 0)
    (V : Set ℝ) (hV : IsOpen V) (h0V : (0:ℝ) ∈ V)
    (hModel : ∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 (t,z) = ell t z • (1:Mat))
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (r C QA QD QJ QB : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hQA : 0 ≤ QA) (hQD : 0 ≤ QD) (hQJ : 0 ≤ QJ) (hQB : 0 ≤ QB)
    (hPoint : RadialAdjointTaylorPointControl
      (commonSupportMatrixFamily 2 A hA S hS hz 0) (commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 0)
      (D 0) (ell 0) r C)
    (hPrincipal : CommonSupportOneBoundaryDerivativeBounds A hA S hS hz (QA*r))
    (hResidual : CommonSupportOneBoundaryTaylorDerivativeBounds A A1 hA hA1 S S1 hS hS1 hz hz1 r (QD*r^2))
    (hForward : ‖fderiv ℝ (fun t => D t-sphereSobolevDegreeL-r •
      (radialCorrectionCovectorL (ell t)).comp (sphereSobolevInclusionL 1 0 (by norm_num))) 0‖ ≤ QJ*r^2)
    (hFirst : ‖fderiv ℝ (fun t => radialCorrectionCovectorL (ell t)) 0‖ ≤ QB) :
    ‖fderiv ℝ (fun t => radialAdjointFromResponseL (commonSupportMatrixFamily 2 A hA S hS hz t) (D t)-
      sphereSobolevDegreeL-r • (radialCorrectionCovectorL (ell t)).adjoint.comp
        (sphereSobolevInclusionL 1 0 (by norm_num))) 0‖ ≤
      radialAdjointJetBudget C*radialAdjointDerivativeBudget QA QD QJ QB*r^2 := by
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let F1 := commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1
  let M0 := fun t => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (F t))))
  let M01 := fun t => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (F1 t))))
  let M1 := fun t => oneBoundaryCoefficientMulL (normalCoefficientJet (F t))
  let M11 := fun t => oneBoundaryCoefficientMulL (normalCoefficientJet (F1 t))
  let T := fun t => coarseBoundaryTangentialL (fun j => tangentCoefficientJet (F t) j)
  let Td := fun t => adjointBoundaryTangentialL (fun j => tangentCoefficientJet (F t) j)
  let B := fun t => radialCorrectionCovectorL (ell t)
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let BI := fun t => (B t).comp I0
  let BaI := fun t => (B t).adjoint.comp I0
  let H := fun t => (M1 t).inverse
  let q := radialAdjointDerivativeBudget QA QD QJ QB
  have hCG := boundaryTangentialCoarseBudget_nonneg
  have hCA := boundaryTangentialAdjointBudget_nonneg
  have hCGQ := mul_nonneg hCG hQD
  have hCAQ := mul_nonneg hCA hQD
  have hSizes : 0 ≤ q ∧ 36*QA ≤ q ∧ (73*36)*QA ≤ q ∧ 36*QD ≤ q ∧ (73*36)*QD ≤ q ∧
      boundaryTangentialCoarseBudget*(78*QD) ≤ q ∧ boundaryTangentialAdjointBudget*((73*78)*QD) ≤ q ∧
      QJ ≤ q ∧ QB ≤ q := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      dsimp [q,radialAdjointDerivativeBudget] <;> nlinarith only [hQA,hQD,hQJ,hQB,hCGQ,hCAQ]
  obtain ⟨hq,hqA0,hqA1,hqQ0,hqQ1,hqT,hqTd,hqJ,hqB⟩ := hSizes
  have hM0S : ContDiff ℝ ∞ M0 := contDiff_commonSupport_coarseNormalMul A hA S hS hz
  have hM01S : ContDiff ℝ ∞ M01 := contDiff_commonSupport_coarseNormalMul A1 hA1 S1 hS1 hz1
  have hM1S : ContDiff ℝ ∞ M1 := contDiff_commonSupport_oneNormalMul A hA S hS hz
  have hM11S : ContDiff ℝ ∞ M11 := contDiff_commonSupport_oneNormalMul A1 hA1 S1 hS1 hz1
  have hTS : ContDiff ℝ ∞ T := contDiff_commonSupport_coarseBoundaryTangential A hA S hS hz
  have hTdS : ContDiff ℝ ∞ Td := contDiff_commonSupport_adjointBoundaryTangential A hA S hS hz
  have hB : DifferentiableAt ℝ B 0 := radialCorrectionCovectorL.differentiableAt.comp 0 hEll
  let J : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
  have hBa : DifferentiableAt ℝ (fun t => (B t).adjoint) 0 := J.differentiableAt.comp 0 hB
  have hJB : ‖fderiv ℝ (fun t => (B t).adjoint) 0‖ ≤ QB := by
    have hJ : ‖J‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro L
      change ‖L.adjoint‖ ≤ 1*‖L‖
      simpa only [one_mul] using (ContinuousLinearMap.adjoint.norm_map L).le
    have hDer := (J.hasFDerivAt.comp 0 hB.hasFDerivAt).fderiv
    apply (congrArg norm hDer).le.trans
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hJ hFirst (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hIncl (G : ℝ → SphereSobolev 0 →L[ℝ] SphereSobolev 0)
      (hG : DifferentiableAt ℝ G 0) (hDG : ‖fderiv ℝ G 0‖ ≤ QB) :
      ‖fderiv ℝ (fun t => (G t).comp I0) 0‖ ≤ QB := by
    have h := norm_fderiv_clm_comp_le G (fun _ : ℝ => I0) 0 hG (differentiableAt_const _)
    simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero] at h
    exact h.trans ((mul_le_mul hDG (norm_sphereSobolevInclusionL_le 1 0 (by norm_num))
      (norm_nonneg _) hQB).trans_eq (mul_one _))
  have hBI : DifferentiableAt ℝ BI 0 := hB.clm_comp (differentiableAt_const _)
  have hBaI : DifferentiableAt ℝ BaI 0 := hBa.clm_comp (differentiableAt_const _)
  let W := V ∩ {t : ℝ | (M1 t).IsInvertible}
  have hW : IsOpen W := hV.inter (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hM1S.continuous)
  have h0W : (0:ℝ) ∈ W := ⟨h0V,hPoint.normal_invertible⟩
  have hInv : ∀ t ∈ W,(M1 t).IsInvertible := fun _ h => h.2
  have hH : DifferentiableAt ℝ H 0 :=
    ((contDiffOn_banachInverseFamily M1 W hM1S.contDiffOn hInv).contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)
  have hFirstId (t : ℝ) (ht : t ∈ W) : BaI t = BI t+(M01 t).comp sphereSobolevDegreeL-sphereSobolevDegreeL.comp (M11 t) := by
    have ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F1 t) z) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens) := by
      rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact commonSupportEnergyMemLp A1 hA1 t
    exact first_radial_adjoint_correction_normalized F0 (F1 t) (ell t) hF0 (by
      intro z hzB i j
      have hMat : coefficientMatrixField 2 (F1 t) z = ell t z • (1:Mat) :=
        (congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 t) z).trans
          (hModel t ht.1 z hzB)
      exact congrArg (fun N : Mat => N i j) hMat) ha1 hInv0
  have hDM0 : ‖fderiv ℝ M0 0‖ ≤ q*r :=
    hPrincipal.coarseNormal.trans ((mul_le_mul_of_nonneg_right hqA0 hr).trans' (by ring_nf;exact le_rfl))
  have hDM1 : ‖fderiv ℝ M1 0‖ ≤ q*r :=
    hPrincipal.oneNormal.trans ((mul_le_mul_of_nonneg_right hqA1 hr).trans' (by ring_nf;exact le_rfl))
  have hDQ0 : ‖fderiv ℝ (fun t => M0 t-ContinuousLinearMap.id ℝ (SphereSobolev 0)-r • M01 t) 0‖ ≤ q*r^2 := by
    exact hResidual.coarseNormal.trans ((mul_le_mul_of_nonneg_right hqQ0 (sq_nonneg r)).trans' (by ring_nf;exact le_rfl))
  have hDQ1 : ‖fderiv ℝ (fun t => M1 t-ContinuousLinearMap.id ℝ (SphereSobolev 1)-r • M11 t) 0‖ ≤ q*r^2 := by
    exact hResidual.oneNormal.trans ((mul_le_mul_of_nonneg_right hqQ1 (sq_nonneg r)).trans' (by ring_nf;exact le_rfl))
  have hDT : ‖fderiv ℝ T 0‖ ≤ q*r^2 :=
    hResidual.tangent.trans ((mul_le_mul_of_nonneg_right hqT (sq_nonneg r)).trans' (by ring_nf;exact le_rfl))
  have hDTd : ‖fderiv ℝ Td 0‖ ≤ q*r^2 :=
    hResidual.adjointTangent.trans ((mul_le_mul_of_nonneg_right hqTd (sq_nonneg r)).trans' (by ring_nf;exact le_rfl))
  have hBound := norm_radial_adjoint_taylor_derivative_le M0 M01 M1 M11 H D BI BaI T Td sphereSobolevDegreeL
    0 W hW h0W r C q hr hr1 hC hq
    (hM0S.differentiable (by simp) 0) (hM01S.differentiable (by simp) 0)
    (hM1S.differentiable (by simp) 0) (hM11S.differentiable (by simp) 0)
    hD hBI hBaI (hTS.differentiable (by simp) 0) (hTdS.differentiable (by simp) 0) hH hInv (fun _ _ => rfl)
    hFirstId hPoint.coarse_normal norm_sphereSobolevDegreeL_le_two hPoint.first_forward hPoint.first_adjoint
    hPoint.forward_remainder hPoint.coarse_remainder hPoint.one_remainder hPoint.coarse_difference
    hPoint.tangent hPoint.adjoint_tangent hPoint.inverse hPoint.inverse_difference hDM0 hDM1
    (hForward.trans (mul_le_mul_of_nonneg_right hqJ (sq_nonneg r))) hDQ0 hDQ1
    ((hIncl B hB hFirst).trans hqB) ((hIncl _ hBa hJB).trans hqB) hDT hDTd
  exact hBound

end ShrinkingSpheres
