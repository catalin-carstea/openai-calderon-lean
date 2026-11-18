import Proof.OperatorInverseTaylorDerivative
import Proof.OperatorTripleTaylorDerivative
import Proof.RadialMultiplierRemainderGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

def uniformInverseTaylorBudget (C : ℝ) : ℝ := C*(C+C*C*C)*C

def uniformInverseTaylorDerivativeBudget (C : ℝ) : ℝ :=
  C*((C+C*C*C+C*C*C)*C+C*uniformInverseTaylorBudget C)

def nativeMultiplierTaylorDerivativeBudget (C : ℝ) : ℝ :=
  let H := ‖fixedHarmonicH1LiftL‖
  let DI := C*C*C
  let DQ := uniformInverseTaylorDerivativeBudget C
  ‖fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL‖*
    (DI*(C*C+(C+C)*C+C*H)+C*(C*C+C*C+C*C+C*C+C*H)+
      DI*(C*C+C*H)+DI*(C*C+C*H)+DQ*(C*H))

/-- Native conditional caller for the gained boundary Taylor derivative.
Every quantitative premise is about the SAME actual inverse, multiplier
forcing and weak Poisson maps. Actual geometric forcing derivative producers
supply the K-premises; no target remainder estimate is assumed. -/
theorem native_half_multiplier_taylor_derivative_le
    (F F1 : ℝ → SmoothCoefficientMatrix 2) (F0 : SmoothCoefficientMatrix 2)
    (ha : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F1 t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (Q : SmoothCoefficientJets 3) (r C : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (U : Set ℝ) (hU : IsOpen U) (h0U : (0:ℝ) ∈ U)
    (hInv : ∀ t ∈ U,(strongDirichletOperator fixedSobolevCalculus 0 (F t)).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (hA : DifferentiableAt ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)) 0)
    (hA1 : DifferentiableAt ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F1 t)) 0)
    (hI : DifferentiableAt ℝ (fun t => (strongDirichletOperator fixedSobolevCalculus 0 (F t)).inverse) 0)
    (hK : DifferentiableAt ℝ (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q) 0)
    (hK1 : DifferentiableAt ℝ (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q) 0)
    (hW : DifferentiableAt ℝ (fun t => nativeWeakHalfLift (coefficientMatrixField 2 (F t)) 0 0 (ha t) sphereFischerInner) 0)
    (hW1 : DifferentiableAt ℝ (fun t => weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 t)) (ha1 t)) 0)
    (hNI : ‖(strongDirichletOperator fixedSobolevCalculus 0 (F 0)).inverse‖ ≤ C)
    (hNI0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ C)
    (hDA : ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)) 0‖ ≤ C*r)
    (hADiff : ‖strongDirichletOperator fixedSobolevCalculus 0 (F 0)-strongDirichletOperator fixedSobolevCalculus 0 F0‖ ≤ C*r)
    (hNA1 : ‖strongDirichletOperator fixedSobolevCalculus 0 (F1 0)‖ ≤ C)
    (hDA1 : ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F1 t)) 0‖ ≤ C)
    (hAR : ‖strongDirichletOperator fixedSobolevCalculus 0 (F 0)-strongDirichletOperator fixedSobolevCalculus 0 F0-
      r • strongDirichletOperator fixedSobolevCalculus 0 (F1 0)‖ ≤ C*r^2)
    (hDAR : ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)-strongDirichletOperator fixedSobolevCalculus 0 F0-
      r • strongDirichletOperator fixedSobolevCalculus 0 (F1 t)) 0‖ ≤ C*r^2)
    (hNK : ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F 0) (fun _ => 0) Q‖ ≤ C)
    (hNK0 : ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q‖ ≤ C)
    (hDK : ‖fderiv ℝ (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q) 0‖ ≤ C*r)
    (hKDiff : ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F 0) (fun _ => 0) Q-
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q‖ ≤ C*r)
    (hNK1 : ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 0) (fun _ => 0) Q‖ ≤ C)
    (hDK1 : ‖fderiv ℝ (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q) 0‖ ≤ C)
    (hKR : ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F 0) (fun _ => 0) Q-
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q-
      r • nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 0) (fun _ => 0) Q‖ ≤ C*r^2)
    (hDKR : ‖fderiv ℝ (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q-
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q-
      r • nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q) 0‖ ≤ C*r^2)
    (hNW1 : ‖weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 0)) (ha1 0)‖ ≤ C)
    (hDW1 : ‖fderiv ℝ (fun t => weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 t)) (ha1 t)) 0‖ ≤ C)
    (hWR : ‖nativeWeakHalfLift (coefficientMatrixField 2 (F 0)) 0 0 (ha 0) sphereFischerInner-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 0)) (ha1 0)‖ ≤ C*r^2)
    (hDWR : ‖fderiv ℝ (fun t => nativeWeakHalfLift (coefficientMatrixField 2 (F t)) 0 0 (ha t) sphereFischerInner-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 t)) (ha1 t)) 0‖ ≤ C*r^2) :
    ‖fderiv ℝ (fun t => radialTaylorMultiplierCommutatorL (F t) F0 (F1 t) (ha t) ha0 (ha1 t) Q r) 0‖ ≤
      nativeMultiplierTaylorDerivativeBudget C*r^2 := by
  let A := fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
  let A1 := fun t => strongDirichletOperator fixedSobolevCalculus 0 (F1 t)
  let I := fun t => (A t).inverse
  let I1 := fun t => -(A0.inverse.comp ((A1 t).comp A0.inverse))
  let K := fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
  let K1 := fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q
  let W := fun t => nativeWeakHalfLift (coefficientMatrixField 2 (F t)) 0 0 (ha t) sphereFischerInner
  let W1 := fun t => weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 t)) (ha1 t)
  let T := fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL
  let IR := uniformInverseTaylorBudget C
  let DR := uniformInverseTaylorDerivativeBudget C
  let DI := C*C*C
  have hIR : 0 ≤ IR := by dsimp [IR,uniformInverseTaylorBudget];positivity
  have hDR : 0 ≤ DR := by dsimp [DR,uniformInverseTaylorDerivativeBudget,uniformInverseTaylorBudget];positivity
  have hDI : 0 ≤ DI := by dsimp [DI];positivity
  have hI1 : DifferentiableAt ℝ I1 0 :=
    ((differentiableAt_const A0.inverse).clm_comp (hA1.clm_comp (differentiableAt_const A0.inverse))).neg
  have hIRNorm : ‖I 0-A0.inverse-r • I1 0‖ ≤ IR*r^2 :=
    norm_operator_inverse_affine_remainder_le (A 0) A0 (A1 0) (hInv 0 h0U) hInv0
      r C C C C C hr hC hC hC hC hC hNI hNI0 hADiff hNA1 hAR
  have hDIR : ‖fderiv ℝ (fun t => I t-A0.inverse-r • I1 t) 0‖ ≤ DR*r^2 :=
    norm_operator_inverse_taylor_remainder_derivative_le A A1 A0 0 U hU h0U hA hA1 hI hInv hInv0
      r C C C C C C C IR hr hr1 hC hC hC hC hC hC hC hIR hNI hNI0 hDA hADiff hNA1 hDA1 hDAR hIRNorm
  have hIDiff : ‖I 0-A0.inverse‖ ≤ DI*r :=
    (norm_inverse_sub_le (A 0) A0 (hInv 0 h0U) hInv0 C C (C*r) hC hC (by positivity) hNI hNI0 hADiff).trans_eq
      (by dsimp only [DI];ring)
  have hIdentity : (fun t => (A t).comp (I t)) =ᶠ[𝓝 (0:ℝ)] (fun _ => ContinuousLinearMap.id ℝ (BallSobolev 0)) := by
    filter_upwards [hU.mem_nhds h0U] with t ht
    exact (hInv t ht).self_comp_inverse
  have hDInv : ‖fderiv ℝ I 0‖ ≤ DI*r := by
    have h := norm_operator_derivative_of_rectangular_left_identity A I (fun _ : ℝ => ContinuousLinearMap.id ℝ (BallSobolev 0))
      0 hA hI hIdentity (hInv 0 h0U) C (C*r) C 0 hC (by positivity) hC le_rfl hNI hDA hNI (by simp)
    exact h.trans_eq (by dsimp only [DI];ring)
  have hTriple := norm_operator_triple_taylor_remainder_derivative_le I I1 A0.inverse K K1 K0 W W1 fixedHarmonicH1LiftL 0
    r C DI DI DR C C C C C C C C C C C hr hr1 hC hDI hDI hDR hC hC hC hC hC hC hC hC hC hC hC
    hI hI1 hK hK1 hW hW1 hNI hDInv hIDiff hDIR hNK hDK hKDiff hNK1 hDK1 hKR hDKR hNW1 hDW1 hWR hDWR
  let Rest := fun t => (I t).comp ((K t).comp (W t))-A0.inverse.comp (K0.comp fixedHarmonicH1LiftL)-
    r • (A0.inverse.comp (K0.comp (W1 t)+(K1 t).comp fixedHarmonicH1LiftL)+(I1 t).comp (K0.comp fixedHarmonicH1LiftL))
  have hFirstDiff : DifferentiableAt ℝ (fun t => A0.inverse.comp (K0.comp (W1 t)+(K1 t).comp fixedHarmonicH1LiftL)+
      (I1 t).comp (K0.comp fixedHarmonicH1LiftL)) 0 :=
    ((differentiableAt_const A0.inverse).clm_comp
      (((differentiableAt_const K0).clm_comp hW1).add (hK1.clm_comp (differentiableAt_const fixedHarmonicH1LiftL)))).add
      (hI1.clm_comp (differentiableAt_const (K0.comp fixedHarmonicH1LiftL)))
  have hRest : DifferentiableAt ℝ Rest 0 :=
    ((hI.clm_comp (hK.clm_comp hW)).sub_const _).sub (hFirstDiff.const_smul r)
  have hW0 : nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner = fixedHarmonicH1LiftL :=
    (nativeWeakHalfLift_congr_unitBall ha0 (flatCoefficientBound 1) (by intro z hz;simpa using hFlat z hz)).trans
      (nativeWeakHalfLift_flat_eq 1 (flatCoefficientBound 1))
  have hFun : (fun t => radialTaylorMultiplierCommutatorL (F t) F0 (F1 t) (ha t) ha0 (ha1 t) Q r) =
      fun t => T.comp (Rest t) := by
    funext t
    rw [radialTaylorMultiplierCommutatorL,halfRadialMultiplierCommutator_trace_product,
      halfRadialMultiplierCommutator_trace_product,hW0]
    change (T.comp ((I t).comp ((K t).comp (W t)))+_)-
      (T.comp (A0.inverse.comp (K0.comp fixedHarmonicH1LiftL))+_)-
      r • T.comp (A0.inverse.comp (K0.comp (W1 t)+(K1 t).comp fixedHarmonicH1LiftL)+
        (I1 t).comp (K0.comp fixedHarmonicH1LiftL)) = T.comp (Rest t)
    dsimp only [Rest]
    simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
    abel
  rw [hFun]
  have hTrace := norm_fderiv_clm_comp_le (fun _ : ℝ => T) Rest 0 (differentiableAt_const T) hRest
  simp only [fderiv_const_apply,norm_zero,zero_mul,zero_add] at hTrace
  have hK0H : ‖K0.comp fixedHarmonicH1LiftL‖ ≤ C*‖fixedHarmonicH1LiftL‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hNK0 (norm_nonneg _))
  have hRestBound : ‖fderiv ℝ Rest 0‖ ≤
      (DI*(C*C+(C+C)*C+C*‖fixedHarmonicH1LiftL‖)+C*(C*C+C*C+C*C+C*C+C*‖fixedHarmonicH1LiftL‖)+
        DI*(C*C+C*‖fixedHarmonicH1LiftL‖)+DI*(C*C+C*‖fixedHarmonicH1LiftL‖)+DR*(C*‖fixedHarmonicH1LiftL‖))*r^2 :=
    hTriple.trans (by gcongr)
  exact hTrace.trans ((mul_le_mul_of_nonneg_left hRestBound (norm_nonneg T)).trans_eq (by
    dsimp only [nativeMultiplierTaylorDerivativeBudget,T,DI,DR]
    ring))

end ShrinkingSpheres
