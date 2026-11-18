import Proof.CommonSupportClosedMovingMultiplierHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
local instance : CompleteSpace (SphereSobolev (1/2:ℝ)) := lp.completeSpace
local instance : CompleteSpace (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) := by infer_instance
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiffAt_commonSupportNativeClosedMultiplierKernel
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (p : P)
    (hStrong : (strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible)
    (hWeak : (commonSupportZeroWeakEnergy a ha p).IsInvertible) :
    ContDiffAt ℝ ∞ (commonSupportNativeClosedMultiplierKernel a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r) p := by
  let Ext := denseIsometryOperatorExtensionL
    (V:=SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (smoothCoefficientClosureInclusionL 3) (denseRange_smoothCoefficientClosureInclusionL 3) (fun _ _ => rfl)
  have hh := Ext.contDiff.contDiffAt.comp p
    (contDiffAt_commonSupportNativeMultiplierKernelInMultiplierL a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p hStrong hWeak)
  exact hh

theorem contDiffAt_commonSupportNativeClosedMovingMultiplierKernel
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (p : P)
    (hStrong : (strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible)
    (hWeak : (commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (Q : P → ClosedCoefficientJets 3) (hQ : ContDiffAt ℝ ∞ Q p) :
    ContDiffAt ℝ ∞ (fun t => commonSupportNativeClosedMultiplierKernel a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r t (Q t)) p :=
  (contDiffAt_commonSupportNativeClosedMultiplierKernel a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p hStrong hWeak).clm_apply hQ

end ShrinkingSpheres
