import Proof.CommonSupportMultiplierForcingRegularity
import Proof.CommonSupportMultiplierGainFactorRegularity
import Proof.CommonSupportWeakFamilyIdentities
import Proof.MultiplierFirstVariationKernel
import Proof.CommonSupportPoissonRegularity
import Proof.CommonSupportWeakPoissonRegularity
import Proof.RadialAdjointMultiplierGain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The SAME actual gained Taylor family is smooth on its genuine strong
and weak inverse locus, with an independently varying radius. The negative
dual-adjoint family is smooth as the fixed continuous-linear image. -/
theorem contDiffOn_commonSupport_multiplier_gain
    (A A1 : P × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → A (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → A1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2)
    (ha : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A hA S hS hz p) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 p) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) (r : P → ℝ) (V : Set P) (hr : ContDiffOn ℝ ∞ r V)
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) :
    let G := fun p => radialTaylorMultiplierCommutatorL
      (commonSupportMatrixFamily 2 A hA S hS hz p) F0
      (commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 p) (ha p) ha0 (ha1 p) Q (r p)
    ContDiffOn ℝ ∞ G V ∧
      ContDiffOn ℝ ∞ (fun p => -realHalfOperatorAdjointL (G p)) V := by
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let F1 := commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1
  let I := fun p => (strongDirichletOperator fixedSobolevCalculus 0 (F p)).inverse
  let I0 := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
  let A1op := fun p => strongDirichletOperator fixedSobolevCalculus 0 (F1 p)
  let K := fun p => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F p) (fun _ => 0) Q
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
  let K1 := fun p => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 p) (fun _ => 0) Q
  let W := fun p => nativeWeakHalfLift (coefficientMatrixField 2 (F p)) 0 0 (ha p) sphereFischerInner
  let W1 := fun p => weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 p)) (ha1 p)
  let T := fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL
  obtain ⟨hIS,hA1S,hWS,hW1S⟩ := contDiffOn_commonSupport_multiplier_native_factors
    A A1 hA hA1 S S1 hS hS1 hz hz1 ha ha1 V hStrong hCoercive
  have hKS : ContDiff ℝ ∞ K := contDiff_commonSupport_bulkMultiplierForcing A hA S hS hz Q
  have hK1S : ContDiff ℝ ∞ K1 := contDiff_commonSupport_bulkMultiplierForcing A1 hA1 S1 hS1 hz1 Q
  let I1 := fun p => -(I0.comp ((A1op p).comp I0))
  have hI1S : ContDiff ℝ ∞ I1 :=
    (contDiff_const.clm_comp (hA1S.clm_comp contDiff_const)).neg
  have hFirstS : ContDiff ℝ ∞ (fun p => halfMultiplierFirstVariationL F0 (F1 p) (ha1 p) Q) := by
    have hFun : (fun p => halfMultiplierFirstVariationL F0 (F1 p) (ha1 p) Q) =
        fun p => T.comp (I0.comp (K0.comp (W1 p)+(K1 p).comp fixedHarmonicH1LiftL)+
          (I1 p).comp (K0.comp fixedHarmonicH1LiftL)) := by
      funext p
      rfl
    rw [hFun]
    exact contDiff_const.clm_comp
      ((contDiff_const.clm_comp ((contDiff_const.clm_comp hW1S).add
        (hK1S.clm_comp contDiff_const))).add (hI1S.clm_comp contDiff_const))
  have hHalfS : ContDiffOn ℝ ∞ (fun p => halfRadialMultiplierCommutatorL (F p) (ha p) Q) V := by
    have hFun : (fun p => halfRadialMultiplierCommutatorL (F p) (ha p) Q) =
        fun p => T.comp ((I p).comp ((K p).comp (W p)))+
          nativeHalfNormalDerivativeMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
            denseSphereHarmonics fixedUnitBallValueTrace Q := by
      funext p
      exact halfRadialMultiplierCommutator_trace_product (F p) (ha p) Q
    rw [hFun]
    exact (contDiffOn_const.clm_comp (hIS.clm_comp (hKS.contDiffOn.clm_comp hWS))).add contDiffOn_const
  let G := fun p => radialTaylorMultiplierCommutatorL (F p) F0 (F1 p) (ha p) ha0 (ha1 p) Q (r p)
  have hGS : ContDiffOn ℝ ∞ G V := (hHalfS.sub contDiffOn_const).sub (hr.smul hFirstS.contDiffOn)
  exact ⟨hGS,(-realHalfOperatorAdjointL).contDiff.comp_contDiffOn hGS⟩

end ShrinkingSpheres
