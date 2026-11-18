import Proof.NativeTaylorScalarCommutator
import Proof.ClosedCoefficientAngularGenerators
import Proof.ClosedHalfScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}

lemma forwardTaylor_closed_scalar_commutator_graph
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (Q : ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((q.scalarMultiplierKernel F0 Q p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
    (t.forwardTaylor p).comp (closedOneBoundaryScalarMultiplierL Q)-
      (closedThreeJetCoarseScalarMultiplierL Q).comp (t.forwardTaylor p) := by
  have hKC : Continuous (fun Q => q.scalarMultiplierKernel F0 Q p) :=
    (commonSupportNativeClosedMultiplierKernel q.a q.a1 q.smooth q.firstSmooth
      q.support q.support q.compact q.compact q.supported q.firstSupported F0 (d.radius y) p).continuous
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        ((q.scalarMultiplierKernel F0 Q p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
      (t.forwardTaylor p).comp (closedOneBoundaryScalarMultiplierL Q)-
        (closedThreeJetCoarseScalarMultiplierL Q).comp (t.forwardTaylor p) := by
    rintro _ ⟨Q,rfl⟩
    rw [closedOneBoundaryScalarMultiplierL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth]
    exact t.forwardTaylor_scalar_commutator_graph V hZ F0 hF0 Q p hp
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) (by fun_prop)) Q

lemma adjointTaylor_closed_scalar_commutator_graph
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (Q : ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      ((t.adjointTaylor p).comp (closedOneBoundaryScalarMultiplierL Q)-
        (closedThreeJetCoarseScalarMultiplierL Q).comp (t.adjointTaylor p)) =
      (-(q.scalarMultiplierKernel F0 Q p).adjoint).comp
        (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  let J : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) →L[ℝ]
      (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    (ContinuousLinearMap.adjoint :
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) ≃ₗᵢ[ℝ]
        (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))).toContinuousLinearEquiv.toContinuousLinearMap
  have hKC : Continuous (fun Q => q.scalarMultiplierKernel F0 Q p) :=
    (commonSupportNativeClosedMultiplierKernel q.a q.a1 q.smooth q.firstSmooth
      q.support q.support q.compact q.compact q.supported q.firstSupported F0 (d.radius y) p).continuous
  have hAC : Continuous (fun Q => -J (q.scalarMultiplierKernel F0 Q p)) :=
    (J.continuous.comp hKC).neg
  have hRC : Continuous (fun Q => (-J (q.scalarMultiplierKernel F0 Q p)).comp
      (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) := hAC.clm_comp continuous_const
  have hDense : ∀ Q ∈ range (smoothCoefficientClosureInclusionL 3),
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        ((t.adjointTaylor p).comp (closedOneBoundaryScalarMultiplierL Q)-
          (closedThreeJetCoarseScalarMultiplierL Q).comp (t.adjointTaylor p)) =
        (-J (q.scalarMultiplierKernel F0 Q p)).comp
          (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
    rintro _ ⟨Q,rfl⟩
    rw [closedOneBoundaryScalarMultiplierL_on_smooth,closedThreeJetCoarseScalarMultiplierL_on_smooth]
    exact t.adjointTaylor_scalar_commutator_graph V hZ F0 hF0 Q p hp
  exact (denseRange_smoothCoefficientClosureInclusionL 3).induction hDense
    (isClosed_eq (by fun_prop) hRC) Q
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
