import Proof.UniformNativeRadialAdjointDefect
import Proof.NativeFirstScalarNegativeGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic
private lemma taylor_difference_algebra {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Pa P A R L Ba B : E) (r : ℝ) (hA : A=Pa+L+r • Ba) (hP : P=R-r • B) :
    Pa-P=(A-(R+L))-r • (Ba-B) := by
  rw [hA,hP,smul_sub]
  abel

private lemma taylor_difference_graph {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I0 : E →L[ℝ] F) (I1 : D →L[ℝ] F) (Pa P A R B : D →L[ℝ] E) (K C : F →L[ℝ] F)
    (r : ℝ) (hT : Pa-P=A-R-r • B)
    (hA : I0.comp (A-R)=K.comp I1) (hB : I0.comp B=(-C).comp I1) :
    I0.comp (Pa-P)=(K+r • C).comp I1 := by
  rw [hT,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,hA,hB]
  simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp,ContinuousLinearMap.neg_comp,smul_neg,sub_neg_eq_add]

namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
def antisymmetricTaylorKernel (t : NormalFrameRelativeResponsePacket q)
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Qn Qell : ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  -(closedThreeJetNegativeScalarMultiplierL Qn).inverse.comp
    (t.fullAdjointScalarCommutator F0 ha0 Qn p)+d.radius y • closedNegativeDegreeScalarCommutatorL F0 ha0 Qell

lemma antisymmetricTaylor_graph (t : NormalFrameRelativeResponsePacket q)
    (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (p : NormalFrameRelativeParameter) (hp : p ∈ t.domain) (Qn : ClosedCoefficientJets 3)
    (hDefect : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (t.fullAdjoint p-(t.response p+sphereSobolevDegreeL))=
      (-(closedThreeJetNegativeScalarMultiplierL Qn).inverse.comp
        (t.fullAdjointScalarCommutator F0 ha0 Qn p)).comp
          (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (t.adjointTaylor p-t.forwardTaylor p)=
      (t.antisymmetricTaylorKernel F0 ha0 Qn
        (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p).comp
          (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  have hFirst := t.firstScalar_negative_graph hZ F0 hF0 ha0 hInv0 Q hQ p hp
  have hB : coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)=
      radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p) := by
    rw [coarseFirstRadialVariationL_normalized_covector,inv_one,one_smul]
  have hForward : t.forwardTaylor p=t.response p-d.radius y •
      (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
        (sphereSobolevInclusionL 1 0 (by norm_num)) :=
    congrArg (fun BB : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => t.response p-d.radius y •
      BB.comp (sphereSobolevInclusionL 1 0 (by norm_num))) hB
  have hDecomp := taylor_difference_algebra (t.adjointTaylor p) (t.forwardTaylor p) (t.fullAdjoint p)
    (t.response p) sphereSobolevDegreeL
    ((radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))
    ((radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))) (d.radius y)
    (t.fullAdjoint_taylor_decomposition p) hForward
  have hFirst' : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      ((radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
        (sphereSobolevInclusionL 1 0 (by norm_num))-
       (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
        (sphereSobolevInclusionL 1 0 (by norm_num)))=
      (-(closedNegativeDegreeScalarCommutatorL F0 ha0
        (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)))).comp
          (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
    simpa only [ContinuousLinearMap.sub_comp] using hFirst
  exact taylor_difference_graph _ _ _ _ _ _ _ _ _ _ hDecomp hDefect hFirst'
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
