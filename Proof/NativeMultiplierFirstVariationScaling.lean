import Proof.NativeHalfMultiplierTaylorScaledDerivative
import Proof.MultiplierFirstVariationKernel

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
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

lemma nativeBulkMultiplierForcing_coefficient_smul (F : SmoothCoefficientMatrix 2)
    (c : ℝ) (Q : SmoothCoefficientJets 3) :
    nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (c • F) (fun _ => 0) Q =
      c • nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q := by
  have h := nativeBulkMultiplierForcing_affine_on_ball fixedSobolevCalculus (c • F) F F Q (c-1) (by
    intro z hz i j
    change coefficientValue 2 (c • F i j) z = _
    rw [coefficientValue_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring)
  exact h.trans (by module)

lemma weakFirstPoissonVariation_coefficient_smul (F : SmoothCoefficientMatrix 2) (c d : ℝ)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hda : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (d • F) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    weakFirstPoissonVariationL c (coefficientMatrixField 2 (d • F)) hda =
      d • weakFirstPoissonVariationL c (coefficientMatrixField 2 F) ha := by
  have hE := nativeWeakEnergy_affine_eq hda ha ha (d-1) (by
    intro z hz
    rw [coefficientMatrixField_smul]
    module)
  have hES : nativeCoefficientWeakEnergyL (coefficientMatrixField 2 (d • F)) 0 0 hda =
      d • nativeCoefficientWeakEnergyL (coefficientMatrixField 2 F) 0 0 ha := hE.trans (by module)
  dsimp only [weakFirstPoissonVariationL]
  rw [hES]
  exact negative_composition_four_smul
    (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
    (nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c))
    (nativeCoefficientWeakEnergyL (coefficientMatrixField 2 F) 0 0 ha) fixedHarmonicH1LiftL d

/-- The actual native first commutator variation is homogeneous in its SAME
coefficient first model. This reconciles fixed-reference and moving radii. -/
theorem halfMultiplierFirstVariation_coefficient_smul (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hca1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (c • F1) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) :
    halfMultiplierFirstVariationL F0 (c • F1) hca1 Q = c • halfMultiplierFirstVariationL F0 F1 ha1 Q := by
  have hS : strongDirichletOperator fixedSobolevCalculus 0 (c • F1) =
      c • strongDirichletOperator fixedSobolevCalculus 0 F1 :=
    (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul c F1
  have hK := nativeBulkMultiplierForcing_coefficient_smul F1 c Q
  have hP := weakFirstPoissonVariation_coefficient_smul F1 1 c ha1 hca1
  let I0 := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
  let A1 := strongDirichletOperator fixedSobolevCalculus 0 F1
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
  let K1 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Q
  let P1 := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1
  have hChange : halfMultiplierFirstVariationL F0 (c • F1) hca1 Q =
      multiplierFirstVariationKernel I0 (c • A1) K0 (c • K1) (c • P1) :=
    (halfMultiplierFirstVariation_kernel F0 (c • F1) hca1 Q).trans
      (multiplierFirstVariationKernel_congr rfl hS rfl hK hP)
  exact hChange.trans ((multiplierFirstVariationKernel_smul I0 A1 K0 K1 P1 c).trans
    (congrArg (fun U => c • U) (halfMultiplierFirstVariation_kernel F0 F1 ha1 Q).symm))

/-- Scaling the actual first coefficient by c is exactly the same as
scaling the Taylor radius in the first correction by c. -/
theorem radialTaylorMultiplierCommutator_rescale_first (F F0 F1 : SmoothCoefficientMatrix 2)
    (c r : ℝ)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hca1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (c • F1) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) :
    radialTaylorMultiplierCommutatorL F F0 (c • F1) ha ha0 hca1 Q r =
      radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q (r*c) := by
  unfold radialTaylorMultiplierCommutatorL
  rw [halfMultiplierFirstVariation_coefficient_smul F0 F1 c ha1 hca1 Q,smul_smul]

end ShrinkingSpheres
