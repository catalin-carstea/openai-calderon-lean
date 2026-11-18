import Proof.NativeTaylorScalarCommutator
import Proof.SmoothFiniteAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}

lemma NativeRelativeHorizontalTaylorData.scalarMultiplierKernel_three_jets
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3) (BQ : ℝ)
    (hQ : SmoothFiniteJetBound Q ((y,frameVectorLinear d.frame y),0) 3 BQ) :
    SmoothFiniteJetBound (fun p => s.coefficients.scalarMultiplierKernel F0 (Q p) p)
      ((y,frameVectorLinear d.frame y),0) 3
      ((2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)*BQ)*(d.radius y)^2) := by
  have hSmooth := contDiffAt_commonSupportNativeClosedMovingMultiplierKernel
    s.coefficients.a s.coefficients.a1 s.coefficients.smooth s.coefficients.firstSmooth
    s.coefficients.support s.coefficients.support s.coefficients.compact s.coefficients.compact
    s.coefficients.supported s.coefficients.firstSupported F0 (d.radius y) _
    s.point.strong s.point.weak Q hQ.smooth
  have hBQ := hQ.nonneg
  refine ⟨by positivity,hSmooth,?_⟩
  exact s.coefficients.native_closed_multiplier_higher_jets 3 (by norm_num) hCQ hCI hCW hQ.nonneg
    hr hr1 F0 hF0 s.point Q hQ.smooth hQ.bound
end ShrinkingSpheres
