import Proof.MultiplierFirstVariationKernel
import Proof.RadialMultiplierRemainderGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
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

/-- The full gained Taylor product after cancellation of the common normal
multiplier. Its dependence on the three forcing slots is linear. -/
def operatorMultiplierTaylorKernel
    {H U V W Z : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I I0 : V →L[ℝ] W) (A1 : W →L[ℝ] V)
    (K K0 K1 : U →L[ℝ] V) (P P0 P1 : H →L[ℝ] U) (r : ℝ) : H →L[ℝ] Z :=
  T.comp (I.comp (K.comp P))-T.comp (I0.comp (K0.comp P0))-
    r • T.comp (I0.comp (K0.comp P1+K1.comp H0)+
      (-(I0.comp (A1.comp I0))).comp (K0.comp H0))

lemma operatorMultiplierTaylorKernel_forcing_affine
    {H U V W Z : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I I0 : V →L[ℝ] W) (A1 : W →L[ℝ] V)
    (K K0 K1 L L0 L1 : U →L[ℝ] V) (P P0 P1 : H →L[ℝ] U) (r c : ℝ) :
    operatorMultiplierTaylorKernel T H0 I I0 A1 (K+c • L) (K0+c • L0) (K1+c • L1) P P0 P1 r =
      operatorMultiplierTaylorKernel T H0 I I0 A1 K K0 K1 P P0 P1 r+
      c • operatorMultiplierTaylorKernel T H0 I I0 A1 L L0 L1 P P0 P1 r := by
  simp only [operatorMultiplierTaylorKernel,ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp]
  module

lemma radialTaylorMultiplierCommutator_kernel (F F0 F1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) (r : ℝ) :
    radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r = operatorMultiplierTaylorKernel
      (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
      (strongDirichletOperator fixedSobolevCalculus 0 F).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 F1)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Q)
      (nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner)
      (nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner)
      (weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1) r := by
  rw [radialTaylorMultiplierCommutatorL,halfRadialMultiplierCommutator_trace_product,
    halfRadialMultiplierCommutator_trace_product,halfMultiplierFirstVariation_kernel]
  dsimp only [operatorMultiplierTaylorKernel,multiplierFirstVariationKernel]
  abel

end ShrinkingSpheres
