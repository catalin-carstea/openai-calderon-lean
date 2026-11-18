import Proof.NativeHalfMultiplierTaylorDerivative
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

/-- Genuine differentiability of the actual gained commutator follows from
its SAME inverse, forcing and weak-Poisson factors. No derivative bound is
used to assert differentiability. -/
theorem differentiableAt_native_radialTaylorMultiplierCommutator
    (F F1 : ℝ → SmoothCoefficientMatrix 2) (F0 : SmoothCoefficientMatrix 2)
    (ha : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F1 t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) (r : ℝ)
    (hA1 : DifferentiableAt ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F1 t)) 0)
    (hI : DifferentiableAt ℝ (fun t => (strongDirichletOperator fixedSobolevCalculus 0 (F t)).inverse) 0)
    (hK : DifferentiableAt ℝ (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q) 0)
    (hK1 : DifferentiableAt ℝ (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q) 0)
    (hW : DifferentiableAt ℝ (fun t => nativeWeakHalfLift (coefficientMatrixField 2 (F t)) 0 0 (ha t) sphereFischerInner) 0)
    (hW1 : DifferentiableAt ℝ (fun t => weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 t)) (ha1 t)) 0)
 :
    DifferentiableAt ℝ (fun t => radialTaylorMultiplierCommutatorL (F t) F0 (F1 t) (ha t) ha0 (ha1 t) Q r) 0 := by
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
  let I1 := fun t => -(A0.inverse.comp
    ((strongDirichletOperator fixedSobolevCalculus 0 (F1 t)).comp A0.inverse))
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
  let T := fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL
  have hI1 : DifferentiableAt ℝ I1 0 :=
    ((differentiableAt_const A0.inverse).clm_comp (hA1.clm_comp (differentiableAt_const A0.inverse))).neg
  have hFirst : DifferentiableAt ℝ (fun t => halfMultiplierFirstVariationL F0 (F1 t) (ha1 t) Q) 0 := by
    change DifferentiableAt ℝ (fun t => T.comp
      (A0.inverse.comp (K0.comp (weakFirstPoissonVariationL 1 (coefficientMatrixField 2 (F1 t)) (ha1 t))+
        (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q).comp fixedHarmonicH1LiftL)+
        (I1 t).comp (K0.comp fixedHarmonicH1LiftL))) 0
    exact (differentiableAt_const T).clm_comp
      (((differentiableAt_const A0.inverse).clm_comp
        (((differentiableAt_const K0).clm_comp hW1).add
          (hK1.clm_comp (differentiableAt_const fixedHarmonicH1LiftL)))).add
        (hI1.clm_comp (differentiableAt_const (K0.comp fixedHarmonicH1LiftL))))
  have hActual : DifferentiableAt ℝ (fun t => halfRadialMultiplierCommutatorL (F t) (ha t) Q) 0 := by
    simp_rw [halfRadialMultiplierCommutator_trace_product]
    exact ((differentiableAt_const T).clm_comp (hI.clm_comp (hK.clm_comp hW))).add_const _
  exact (hActual.sub_const _).sub (hFirst.const_smul r)

end ShrinkingSpheres
