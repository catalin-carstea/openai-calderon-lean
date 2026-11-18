import Proof.NativeMultiplierForcingMultiplierLinearity
import Proof.MultiplierTaylorGainKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
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
attribute [local irreducible] nativeWeakHalfLift nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

section
variable (F F0 F1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))

/-- The full gained Taylor operator is exactly affine in the scalar
multiplier gradient, for the SAME native coefficient and inverse witnesses. -/
theorem radialTaylorMultiplierCommutator_multiplier_affine_on_ball
    (Q Q0 Q1 : SmoothCoefficientJets 3) (r c : ℝ)
    (h : ∀ z ∈ (ballOpens:Set X),∀ j,
      (gradient (coefficientValue 3 Q) z) j =
        (gradient (coefficientValue 3 Q0) z) j+c*(gradient (coefficientValue 3 Q1) z) j) :
    radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r =
      radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q0 r+
      c • radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q1 r := by
  rw [radialTaylorMultiplierCommutator_kernel,radialTaylorMultiplierCommutator_kernel,
    radialTaylorMultiplierCommutator_kernel]
  rw [nativeBulkMultiplierForcing_multiplier_affine_on_ball fixedSobolevCalculus F Q Q0 Q1 c h,
    nativeBulkMultiplierForcing_multiplier_affine_on_ball fixedSobolevCalculus F0 Q Q0 Q1 c h,
    nativeBulkMultiplierForcing_multiplier_affine_on_ball fixedSobolevCalculus F1 Q Q0 Q1 c h]
  exact operatorMultiplierTaylorKernel_forcing_affine ..

lemma radialTaylorMultiplierCommutator_multiplier_add
    (Q R : SmoothCoefficientJets 3) (r : ℝ) :
    radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 (Q+R) r =
      radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r+
      radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 R r := by
  have h := radialTaylorMultiplierCommutator_multiplier_affine_on_ball F F0 F1 ha ha0 ha1 (Q+R) Q R r 1 (by
    intro z hz j
    rw [coefficientValue_gradient_add]
    simp only [PiLp.add_apply,one_mul])
  simpa only [one_smul] using h

lemma radialTaylorMultiplierCommutator_multiplier_smul
    (Q : SmoothCoefficientJets 3) (r c : ℝ) :
    radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 (c • Q) r =
      c • radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r := by
  have h := radialTaylorMultiplierCommutator_multiplier_affine_on_ball F F0 F1 ha ha0 ha1 (c • Q) Q Q r (c-1) (by
    intro z hz j
    rw [coefficientValue_gradient_smul]
    simp only [PiLp.smul_apply,smul_eq_mul]
    ring)
  simpa only [sub_smul,one_smul,add_sub_cancel] using h

/-- Linearity in the multiplier is an exact native identity, available
before choosing any finite-dimensional family of geometric multipliers. -/
def radialTaylorMultiplierInMultiplierLinear (r : ℝ) :
    SmoothCoefficientJets 3 →ₗ[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) where
  toFun Q := radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r
  map_add' Q R := radialTaylorMultiplierCommutator_multiplier_add F F0 F1 ha ha0 ha1 Q R r
  map_smul' c Q := radialTaylorMultiplierCommutator_multiplier_smul F F0 F1 ha ha0 ha1 Q r c

end
end ShrinkingSpheres
