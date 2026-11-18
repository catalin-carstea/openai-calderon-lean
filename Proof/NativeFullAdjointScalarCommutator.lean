import Proof.NativeClosedScalarCommutator
import Proof.ClosedNegativeDegreeScalarCommutator
import Proof.NativeFullAdjointTaylorDecomposition
import Proof.NegativeScalarCommutatorGraph
import Proof.ClosedNegativeScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
def fullAdjointScalarCommutator (_t : NormalFrameRelativeResponsePacket q)
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  -(q.scalarMultiplierKernel F0 Q p).adjoint+closedNegativeDegreeScalarCommutatorL F0 ha0 Q+
    d.radius y • ((radialCorrectionNegativeAdjointMapL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
      (closedThreeJetNegativeScalarMultiplierL Q)-(closedThreeJetNegativeScalarMultiplierL Q).comp
        (radialCorrectionNegativeAdjointMapL (normalFrameRelativeFirstCovector d.γ d.g₁ p)))

lemma fullAdjoint_closed_scalar_commutator (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    CommutatorLift (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))
      (closedOneBoundaryScalarMultiplierL Q) (closedThreeJetCoarseScalarMultiplierL Q)
      (t.fullAdjoint p) (t.fullAdjointScalarCommutator F0 ha0 Q p) := by
  let B := (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint
  have hB := bounded_coarse_negative_commutator B
    (radialCorrectionNegativeAdjointMapL (normalFrameRelativeFirstCovector d.γ d.g₁ p))
    (closedOneBoundaryScalarMultiplierL Q) (closedThreeJetCoarseScalarMultiplierL Q)
    (closedThreeJetNegativeScalarMultiplierL Q) (radialCorrectionNegativeAdjoint_coarse _)
    (closedThreeJet_scalar_multiplier_compatible Q) (closedThreeJet_negative_scalar_multiplier_coarse Q)
  have hT := t.adjointTaylor_closed_scalar_commutator_graph V hZ F0 hF0 Q p hp
  have hD := degree_closed_scalar_negative_graph F0 ha0
    (fun z hz => hF0 z (unitBall_subset_closedBall_two hz)) hInv0 Q
  have hAll := CommutatorLift.add (CommutatorLift.add hT hD) (CommutatorLift.smul hB (d.radius y))
  rw [t.fullAdjoint_taylor_decomposition p]
  exact hAll
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
