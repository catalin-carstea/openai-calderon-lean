import Proof.MultiplierForcingAffine
import Proof.OperatorInverseAffineTaylor
import Proof.OperatorTripleTaylor
import Proof.StrongAffineOperatorPointBounds
import Proof.NativeWeakTaylorData
import Proof.NativeWeakCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse nativeCoefficientWeakFunctionalInverse

def halfMultiplierFirstVariationL (F0 F1 : SmoothCoefficientMatrix 2)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Qm : SmoothCoefficientJets 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  let I0 := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
  let A1 := strongDirichletOperator fixedSobolevCalculus 0 F1
  let I1 := -(I0.comp (A1.comp I0))
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Qm
  let K1 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Qm
  let P1 := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1
  (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL).comp
    (I0.comp (K0.comp P1+K1.comp fixedHarmonicH1LiftL)+I1.comp (K0.comp fixedHarmonicH1LiftL))

def multiplierInverseTaylorBudget (C P Q : ℝ) : ℝ :=
  C*(strongC1OperatorBudget fixedSobolevCalculus*Q+
    C*(strongC1OperatorBudget fixedSobolevCalculus*(Q+P))*(strongC1OperatorBudget fixedSobolevCalculus*P))*C

def multiplierInverseDifferenceBudget (C P Q : ℝ) : ℝ :=
  C*(strongC1OperatorBudget fixedSobolevCalculus*(Q+P))*C

def halfMultiplierTaylorPointBudget (F0 : SmoothCoefficientMatrix 2) (Qm : SmoothCoefficientJets 3)
    (C P Q q B CP1 CP2 : ℝ) : ℝ :=
  let L := 15*nativeMultiplierForcingGradientBudget*B
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Qm
  let QA := multiplierInverseTaylorBudget C P Q
  let DA := multiplierInverseDifferenceBudget C P Q
  ‖fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL‖*
    (C*((L*q)*CP2+(L*P+L*Q)*CP1+L*Q*‖fixedHarmonicH1LiftL‖)+
      (DA+QA)*(‖K0‖*CP1+L*P*‖fixedHarmonicH1LiftL‖)+QA*‖K0.comp fixedHarmonicH1LiftL‖)

lemma halfRadialMultiplierCommutator_trace_product (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Qm : SmoothCoefficientJets 3) :
    halfRadialMultiplierCommutatorL F ha Qm =
      (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL).comp
        ((strongDirichletOperator fixedSobolevCalculus 0 F).inverse.comp
          ((nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Qm).comp
            (nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner)))+
      nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace Qm := by
  apply ContinuousLinearMap.ext
  intro f
  rfl

/-- The SAME actual gained half-boundary commutator has a quadratic affine
Taylor remainder from only local C1 coefficients and the genuine weak Taylor
packet. Neither a global cutoff norm nor a frame derivative budget occurs. -/
theorem norm_halfMultiplierCommutator_first_remainder_local_C1
    (F F0 F1 : SmoothCoefficientMatrix 2) (Qm : SmoothCoefficientJets 3)
    (r C CW CA Pw Qw CP1 CP2 P Q q B : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hq : 0 ≤ q) (hB : 0 ≤ B) (hCP1 : 0 ≤ CP1) (hCP2 : 0 ≤ CP2)
    (t : NativeWeakTaylorData (coefficientMatrixField 2 F) (coefficientMatrixField 2 F1)
      1 r CW CA Pw Qw CP1 CP2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (hNI : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C)
    (hNI0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ C)
    (hVal1 : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) z| ≤ P)
    (hDer1 : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) z‖ ≤ P)
    (hValR : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-F0-r • F1) i j) z| ≤ Q*r^2)
    (hDerR : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-F0-r • F1) i j)) z‖ ≤ Q*r^2)
    (hValF : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) z| ≤ q)
    (hDerF : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) z‖ ≤ q)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Qm) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Qm) w) j) z‖ ≤ B) :
    ‖halfRadialMultiplierCommutatorL F t.energy.coefficient_bound Qm-
      halfRadialMultiplierCommutatorL F0 ha0 Qm-
      r • halfMultiplierFirstVariationL F0 F1 t.first_coefficient_bound Qm‖ ≤
      halfMultiplierTaylorPointBudget F0 Qm C P Q q B CP1 CP2*r^2 := by
  let A := strongDirichletOperator fixedSobolevCalculus 0 F
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
  let A1 := strongDirichletOperator fixedSobolevCalculus 0 F1
  let I1 := -(A0.inverse.comp (A1.comp A0.inverse))
  let K := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Qm
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Qm
  let K1 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Qm
  let W := nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 t.energy.coefficient_bound sphereFischerInner
  let W1 := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) t.first_coefficient_bound
  let L := 15*nativeMultiplierForcingGradientBudget*B
  let S := strongC1OperatorBudget fixedSobolevCalculus
  let QA := multiplierInverseTaylorBudget C P Q
  let DA := multiplierInverseDifferenceBudget C P Q
  have hG := nativeMultiplierForcingGradientBudget_nonneg
  have hL : 0 ≤ L := by dsimp only [L];positivity
  have hS : 0 ≤ S := strongC1OperatorBudget_nonneg _
  have hQA : 0 ≤ QA := by dsimp only [QA,multiplierInverseTaylorBudget];positivity
  have hDA : 0 ≤ DA := by dsimp only [DA,multiplierInverseDifferenceBudget];positivity
  have hA1 : ‖A1‖ ≤ S*P := norm_strongDirichletOperator_zero_le fixedSobolevCalculus F1 P hP hVal1 hDer1
  have hAR : ‖A-A0-r • A1‖ ≤ (S*Q)*r^2 := by
    have hMap : A-A0-r • A1 = strongDirichletOperator fixedSobolevCalculus 0 (F-F0-r • F1) := by
      change (strongCoefficientOperatorL fixedSobolevCalculus 0) F-
        (strongCoefficientOperatorL fixedSobolevCalculus 0) F0-r • (strongCoefficientOperatorL fixedSobolevCalculus 0) F1 =
        (strongCoefficientOperatorL fixedSobolevCalculus 0) (F-F0-r • F1)
      simp only [(strongCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
        (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul]
    rw [hMap]
    exact (norm_strongDirichletOperator_zero_le fixedSobolevCalculus (F-F0-r • F1) (Q*r^2)
      (by positivity) hValR hDerR).trans_eq (by ring)
  have hADiff : ‖A-A0‖ ≤ (S*(Q+P))*r := by
    have h := (strong_affine_operator_point_bounds fixedSobolevCalculus F F0 F1 1 r P Q hP hQ hr hr1
      hVal1 hDer1 (by simpa only [one_smul] using hValR) (by simpa only [one_smul] using hDerR)).2.1
    simpa only [one_smul] using h
  have hIR : ‖A.inverse-A0.inverse-r • I1‖ ≤ QA*r^2 :=
    norm_operator_inverse_affine_remainder_le A A0 A1 hInv hInv0 r C C (S*(Q+P)) (S*P) (S*Q)
      hr hC hC (by positivity) (by positivity) (by positivity) hNI hNI0 hADiff hA1 hAR
  have hIDiff : ‖A.inverse-A0.inverse‖ ≤ (DA+QA)*r := by
    have h := norm_inverse_sub_le A A0 hInv hInv0 C C (S*(Q+P)*r) hC hC
      (by positivity) hNI hNI0 hADiff
    have hBound : ‖A.inverse-A0.inverse‖ ≤ DA*r := h.trans_eq (by dsimp only [DA,multiplierInverseDifferenceBudget,S];ring)
    exact hBound.trans (by gcongr;exact le_add_of_nonneg_right hQA)
  have hK : ‖K‖ ≤ L*q := norm_nativeBulkMultiplierForcing_local_C1 F Qm q B hq hB hValF
    (by intro i j z hz;rw [TauCeti.norm_gradient_eq_norm_fderiv];exact hDerF i j z hz) hQ1 hQ2
  have hK1 : ‖K1‖ ≤ L*P := norm_nativeBulkMultiplierForcing_local_C1 F1 Qm P B hP hB hVal1
    (by intro i j z hz;rw [TauCeti.norm_gradient_eq_norm_fderiv];exact hDer1 i j z hz) hQ1 hQ2
  have hKR : ‖K-K0-r • K1‖ ≤ (L*Q)*r^2 := norm_nativeBulkMultiplierForcing_affine_remainder_local_C1
    F F0 F1 Qm r Q B hQ hB hValR
    (by intro i j z hz;rw [TauCeti.norm_gradient_eq_norm_fderiv];exact hDerR i j z hz) hQ1 hQ2
  have hKDiff : ‖K-K0‖ ≤ (L*P+L*Q)*r := norm_sub_of_affine_remainder_le K K0 K1 r (L*P) (L*Q)
    hr hr1 (by positivity) (by positivity) hK1 hKR
  have hTriple := norm_operator_triple_taylor_le A.inverse A0.inverse I1 K K0 K1 W fixedHarmonicH1LiftL W1
    r C DA QA (L*q) (L*P) (L*Q) CP1 CP2 hr hC hDA hQA (by positivity) (by positivity) (by positivity)
    hCP1 hCP2 hNI hIDiff hIR hK hKDiff hKR hK1 t.poisson_remainder_bound t.first_poisson_bound
  have hW0 : nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner = fixedHarmonicH1LiftL :=
    (nativeWeakHalfLift_congr_unitBall ha0 (flatCoefficientBound 1) (by intro z hz;simpa using hFlat z hz)).trans
      (nativeWeakHalfLift_flat_eq 1 (flatCoefficientBound 1))
  have hTrace := norm_trace_triple_taylor_le (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL)
    (nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedUnitBallValueTrace Qm) A.inverse A0.inverse I1 K K0 K1 W fixedHarmonicH1LiftL W1 r _ hTriple
  rw [halfRadialMultiplierCommutator_trace_product,halfRadialMultiplierCommutator_trace_product,hW0]
  exact hTrace

end ShrinkingSpheres
