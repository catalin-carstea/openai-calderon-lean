import Proof.OrderOneCoefficientAlgebra
import Proof.Archive.NativeOrderOneCoefficientMultiplierTopology
import Proof.Archive.CompactParameterSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.CompactParameterSmoothness
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiff_coarseSphereScalarMulL_joint (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun p => coarseSphereScalarMulL
      (⟨fun w : UnitSphere => g (p,w.val),hg.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩)) := by
  have hValue := contDiff_infty_compactPullback g hg
    (⟨Subtype.val,continuous_subtype_val⟩ : C(UnitSphere,X))
  have hMul := sphereContinuousScalarMultiplierL.contDiff.comp hValue
  exact contDiff_const.clm_comp (hMul.clm_comp contDiff_const)

theorem contDiff_oneBoundaryCoefficientMulL_commonSupport
    (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → g (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => oneBoundaryCoefficientMulL (commonSupportCoefficientFamily 2 g hg S hS hz p)) := by
  have hSmooth := contDiff_nativeOrderOneCoefficientMulL_commonSupport fixedSobolevCalculus
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace g hg S hS hz
  have hEq (p : P) : oneBoundaryCoefficientMulL (commonSupportCoefficientFamily 2 g hg S hS hz p) =
      nativeOrderOneCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
        denseSphereHarmonics fixedUnitBallValueTrace (commonSupportCoefficientFamily 3 g hg S hS hz p)
        (commonSupportCoefficientFamily 2 g hg S hS hz p)
        (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2 g hg S hS hz p) := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
    have hData : nativeH2CoefficientSmoothData (commonSupportCoefficientFamily 3 g hg S hS hz p) =
        coefficientSmoothData (commonSupportCoefficientFamily 2 g hg S hS hz p) := by
      apply Subtype.ext
      exact coefficientValue_commonSupportCoefficientFamily_order_eq 3 2 g hg S hS hz p
    have hNative := sphereSobolevInclusionL_nativeOrderOneCoefficientMulL_zero fixedSobolevCalculus
      sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
        (commonSupportCoefficientFamily 3 g hg S hS hz p) (commonSupportCoefficientFamily 2 g hg S hS hz p)
        (coefficientValue_commonSupportCoefficientFamily_order_eq 3 2 g hg S hS hz p) u
    rw [hData] at hNative
    exact (oneBoundaryCoefficientMulL_coarse (commonSupportCoefficientFamily 2 g hg S hS hz p) u).trans hNative.symm
  simpa only [← hEq] using hSmooth

end ShrinkingSpheres
