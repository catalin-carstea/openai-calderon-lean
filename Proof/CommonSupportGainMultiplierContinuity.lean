import Proof.NativeMultiplierForcingBilinear
import Proof.MultiplierTaylorGainInMultiplier
import Proof.NativeMultiplierGainMultiplierLinearity
import Proof.CommonSupportMultiplierGainFactorRegularity

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

def radialTaylorMultiplierInMultiplierL (F F0 F1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r : ℝ) : SmoothCoefficientJets 3 →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  operatorMultiplierTaylorInMultiplierL
    (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
    (strongDirichletOperator fixedSobolevCalculus 0 F).inverse
    (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
    (strongDirichletOperator fixedSobolevCalculus 0 F1)
    (nativeBulkMultiplierForcingInMultiplierL F) (nativeBulkMultiplierForcingInMultiplierL F0)
    (nativeBulkMultiplierForcingInMultiplierL F1)
    (nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner)
    (nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner)
    (weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1) r

lemma radialTaylorMultiplierInMultiplierL_apply (F F0 F1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r : ℝ) (Q : SmoothCoefficientJets 3) :
    radialTaylorMultiplierInMultiplierL F F0 F1 ha ha0 ha1 r Q =
      radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r :=
  (operatorMultiplierTaylorInMultiplierL_apply ..).trans (radialTaylorMultiplierCommutator_kernel F F0 F1 ha ha0 ha1 Q r).symm

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma continuous_commonSupport_forcingInMultiplier
    (A : P × X → Mat) (hA : ContDiff ℝ ∞ A) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → A (p,z) = 0) :
    Continuous (fun p => nativeBulkMultiplierForcingInMultiplierL (commonSupportMatrixFamily 2 A hA S hS hz p)) := by
  have hF : Continuous (commonSupportMatrixFamily 2 A hA S hS hz) :=
    continuous_pi (fun i => continuous_pi (fun j =>
      continuous_commonSupportCoefficientFamily 2 (fun p => A p i j)
        (contDiff_pi.mp (contDiff_pi.mp hA i) j) S hS
        (fun p z hzS => by rw [hz p z hzS];rfl)))
  exact nativeBulkMultiplierForcingBilinearL.continuous.comp hF

/-- The actual gained family is continuous in operator norm as a bounded
linear map on all scalar multipliers. This supplies the missing continuity
premise in the moving-multiplier derivative rule. -/
theorem continuousOn_commonSupport_gainInMultiplier
    (A A1 : P × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → A (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → A1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2)
    (ha : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A hA S hS hz p) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 p) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r : ℝ) (V : Set P)
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) :
    ContinuousOn (fun p => radialTaylorMultiplierInMultiplierL
      (commonSupportMatrixFamily 2 A hA S hS hz p) F0
      (commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 p) (ha p) ha0 (ha1 p) r) V := by
  obtain ⟨hI,hA1op,hW,hW1⟩ := contDiffOn_commonSupport_multiplier_native_factors
    A A1 hA hA1 S S1 hS hS1 hz hz1 ha ha1 V hStrong hCoercive
  exact continuousOn_operatorMultiplierTaylorInMultiplierL V
    (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
    (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
    (nativeBulkMultiplierForcingInMultiplierL F0)
    (nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner) r
    _ _ _ _ _ _ hI.continuousOn hA1op.continuous.continuousOn
    (continuous_commonSupport_forcingInMultiplier A hA S hS hz).continuousOn
    (continuous_commonSupport_forcingInMultiplier A1 hA1 S1 hS1 hz1).continuousOn
    hW.continuousOn hW1.continuous.continuousOn

end ShrinkingSpheres
