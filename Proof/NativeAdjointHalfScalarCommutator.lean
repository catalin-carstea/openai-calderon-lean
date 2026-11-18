import Proof.BalancedHigherScalarCommutator
import Proof.NativeHalfTaylorHigherEndpoints
import Proof.ConjugationCancellationFiniteJets
import Proof.HalfScalarCommutatorCorrection
import Proof.SkewHalfEndpointGraph
import Proof.NativeClosedScalarCommutator
import Proof.DenseSkewAdjoint
import Proof.ClosedHalfScalarCompatibility
import Proof.NativeScalarMultiplierKernelJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}

def adjointHalfScalarCommutator (_t : NormalFrameRelativeResponsePacket q)
    (F0 : SmoothCoefficientMatrix 2)
    (KN : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q : ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  halfScalarCommutatorCorrectionL (q.scalarMultiplierKernel F0 Q p) (-(KN p).adjoint)
    (closedThreeJetHalfBoundaryScalarMultiplierL Q)

lemma adjointTaylor_half_scalar_commutator_graph (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (KN : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q : ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (hKN : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (t.adjointTaylor p-t.forwardTaylor p)=
        (KN p).comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((t.adjointHalfScalarCommutator F0 KN Q p).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=
        (t.adjointTaylor p).comp (closedOneBoundaryScalarMultiplierL Q)-
          (closedThreeJetCoarseScalarMultiplierL Q).comp (t.adjointTaylor p) := by
  have hG := t.forwardTaylor_closed_scalar_commutator_graph V hZ F0 hF0 Q p hp
  have hK := skew_negative_half_endpoint_graph (t.adjointTaylor p-t.forwardTaylor p) (KN p)
    (true_adjoint_difference_skew (sphereSobolevInclusionL 1 0 (by norm_num))
      (t.forwardTaylor p) (t.adjointTaylor p) (V.taylorPair p hp)) hKN
  have hM1 : (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))=
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).comp (closedOneBoundaryScalarMultiplierL Q) :=
    ContinuousLinearMap.ext (fun u => (closedThreeJet_scalar_multiplier_one_half Q u).symm)
  have hM0 : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (closedThreeJetHalfBoundaryScalarMultiplierL Q)=
      (closedThreeJetCoarseScalarMultiplierL Q).comp (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) :=
    ContinuousLinearMap.ext (closedThreeJet_half_scalar_multiplier_coarse Q)
  exact half_scalar_commutator_of_difference _ _ _ _ _ _ _ _ _ hG hK hM1 hM0
/-- The SAME half scalar commutator realizes the higher Taylor endpoint
commutator, with an actual inclusion and no additional order loss. -/
lemma adjointHigherTaylor_scalar_commutator_graph (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (KN : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q : ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (hKN : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (t.adjointTaylor p-t.forwardTaylor p)=
        (KN p).comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    (V.adjointHigherTaylor h hK hZ p).comp (closedThreeJetHigherScalarMultiplierL Q)-
      (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp (V.adjointHigherTaylor h hK hZ p)=
        (t.adjointHalfScalarCommutator F0 KN Q p).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact balanced_higher_scalar_commutator (t.adjointTaylor p) (V.adjointHigherTaylor h hK hZ p)
    (t.adjointHalfScalarCommutator F0 KN Q p) Q
    (V.adjointHigherTaylor_coarse_compatible h hK hZ F0 hF0 p hp)
    (t.adjointTaylor_half_scalar_commutator_graph V hZ F0 hF0 KN Q p hp hKN)
end NormalFrameRelativeResponsePacket

lemma NativeRelativeHorizontalTaylorData.adjointHalfScalarCommutator_three_jets
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (KN : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (BK : ℝ) (hKN : SmoothFiniteJetBound KN ((y,frameVectorLinear d.frame y),0) 3 (BK*(d.radius y)^2))
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3) (BQ : ℝ)
    (hQ : SmoothFiniteJetBound Q ((y,frameVectorLinear d.frame y),0) 3 BQ) :
    SmoothFiniteJetBound (fun p => s.response.adjointHalfScalarCommutator F0 KN (Q p) p)
      ((y,frameVectorLinear d.frame y),0) 3
      (((2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)+
        2*(2^3)*BK*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*BQ)*(d.radius y)^2) := by
  have hG := s.scalarMultiplierKernel_three_jets hF0 hCQ hCI hCW hr hr1 Q BQ hQ
  have hK := hKN.adjoint.neg
  have hM := hQ.clm closedThreeJetHalfBoundaryScalarMultiplierL
  have hAll := (hG.add (hK.comp hM)).sub (hM.comp hK)
  have hBudget :
      ((2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)*BQ)*(d.radius y)^2+
        2^3*(BK*(d.radius y)^2)*(‖closedThreeJetHalfBoundaryScalarMultiplierL‖*BQ))+
        2^3*(‖closedThreeJetHalfBoundaryScalarMultiplierL‖*BQ)*(BK*(d.radius y)^2)=
      ((2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)+
        2*(2^3)*BK*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*BQ)*(d.radius y)^2 := by ring
  exact hAll.weaken (le_of_eq hBudget)
end ShrinkingSpheres
