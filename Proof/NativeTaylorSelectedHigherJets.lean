import Proof.UniformNativeRelativeHorizontalTaylorData
import Proof.NativeHalfTaylorHigherRegularity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}

/-- Shared raw native half-Taylor three-jets used by the original generator
producer and the ANY-selected-domain higher Taylor producer. -/
lemma half_taylor_three_jets
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (V : s.response.SymmetricAdjointDomain) (hCQ : 0 ≤ CQ) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    SmoothFiniteJetBound s.coefficients.halfTaylor ((y,frameVectorLinear d.frame y),0) 3
      (|lowRadialTaylorJetBudget 3 2 CW 5 CQ CQ CQ| *(d.radius y)^2) :=
  ⟨by positivity,V.contDiffOn_halfTaylor.contDiffAt (V.domainOpen.mem_nhds V.pointMem),
    s.coefficients.native_half_taylor_higher_jets 3 (by norm_num) hCQ hCW hr hr1 F0 hF0 s.point⟩

/-- Shared SAME-domain higher adjoint Taylor three-jet estimate. The degree
family is supplied for that exact chosen domain. -/
lemma adjoint_higher_taylor_three_jets
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (hCQ : 0 ≤ CQ) (hCW : 0 ≤ CW) (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (CD : ℝ) (hDegree : SmoothFiniteJetBound (V.degreeFamily h hK (by norm_num))
      ((y,frameVectorLinear d.frame y),0) 3 (CD*(d.radius y)^2)) :
    SmoothFiniteJetBound (V.adjointHigherTaylor h hK (by norm_num)) ((y,frameVectorLinear d.frame y),0) 3
      ((|lowRadialTaylorJetBudget 3 2 CW 5 CQ CQ CQ|+CD)*(d.radius y)^2) := by
  have hLow := s.half_taylor_three_jets V hCQ hCW hr hr1 hF0
  have hHigh := (V.higherTaylor_jet_bounds h hK (by norm_num) _ 3 _ _ hLow hDegree).2
  simpa only [add_mul] using hHigh
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
