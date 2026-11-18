import Proof.LinearScalarDegreeCorrection
import Proof.NativeRelativeTrueAdjointDomain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
lemma firstScalar_negative_graph (t : NormalFrameRelativeResponsePacket q)
    (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (p : NormalFrameRelativeParameter) (hp : p ∈ t.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (((radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint-
        radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
          (sphereSobolevInclusionL 1 0 (by norm_num))) =
      (-(closedNegativeDegreeScalarCommutatorL F0 ha0
        (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)))).comp
          (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  let F1 := commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported p
  have hMem : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact commonSupportEnergyMemLp q.a1 q.firstSmooth p
  have hFirst (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) (i j : I) :
      coefficientValue 2 (F1 i j) z=normalFrameRelativeFirstCovector d.γ d.g₁ p z*(1:Mat) i j := by
    change coefficientMatrixField 2 F1 z i j= _
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact congrArg (fun A : Mat => A i j)
      (q.firstScalar p (t.sub hp) z (Metric.closedBall_subset_closedBall hZ hz))
  rw [linearScalarClosedCoefficientL_eq_closure]
  exact first_correction_closed_scalar_negative_graph F0 F1 _ _
    (linearScalarSmoothCoefficient_value Q hQ _) hF0 hFirst ha0 hMem hInv0
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
