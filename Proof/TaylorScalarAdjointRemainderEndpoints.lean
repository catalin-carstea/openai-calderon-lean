import Proof.AdjointDefectEndpointCompatibility
import Proof.NativeScalarKernelEndpointCompatibility
import Proof.NativeFirstErrorAdjointRemainderNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma finite_scalar_remainder_endpoint_compatible {E F κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype κ]
    (I0 : E →L[ℝ] F) (M K C : κ → E →L[ℝ] E) (Mn Kn Cn : κ → F →L[ℝ] F) (sign : κ → ℝ)
    (hM : ∀ a,I0.comp (M a)=(Mn a).comp I0)
    (hK : ∀ a,I0.comp (K a)=(Kn a).comp I0)
    (hC : ∀ a,I0.comp (C a)=(Cn a).comp I0) :
    I0.comp (∑ a,((M a).comp (K a)-sign a • C a))=
      (∑ a,((Mn a).comp (Kn a)-sign a • Cn a)).comp I0 := by
  have hTerm (a : κ) : I0.comp ((M a).comp (K a)-sign a • C a)=
      ((Mn a).comp (Kn a)-sign a • Cn a).comp I0 := by
    have hProd : I0.comp ((M a).comp (K a))=((Mn a).comp (Kn a)).comp I0 := by
      calc
        _ = (I0.comp (M a)).comp (K a) := (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = ((Mn a).comp I0).comp (K a) := congrArg (fun T => T.comp (K a)) (hM a)
        _ = (Mn a).comp (I0.comp (K a)) := ContinuousLinearMap.comp_assoc _ _ _
        _ = (Mn a).comp ((Kn a).comp I0) := congrArg (fun T => (Mn a).comp T) (hK a)
        _ = _ := (ContinuousLinearMap.comp_assoc _ _ _).symm
    rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,hProd,hC a,
      ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun a _ => DFunLike.congr_fun (hTerm a) u)

def taylorScalarAdjointRemainderHalfL
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (C : TaylorGeneratorIndex → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ a,((closedThreeJetHalfBoundaryScalarMultiplierL (Q a)).comp (taylorGeneratorAdjointDefectHalfL KN a)-
    a.adjointSign • C a)

lemma NativeTaylorGeneratorBounds.scalar_adjoint_remainder_half_negative_compatible
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (A : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (taylorScalarAdjointRemainderHalfL KN (fun a => taylorGeneratorScalarCommutator A.scalar F0 ha0 a (Q a)) Q)=
      (taylorScalarAdjointRemainderL KN (fun a => nativeNegativeScalarGeneratorCommutator s ha0 p a (Q a)) Q).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) :=
  finite_scalar_remainder_endpoint_compatible _ _ _ _ _ _ _ TaylorGeneratorIndex.adjointSign
    (fun a => ContinuousLinearMap.ext (closedThreeJet_half_negative_scalar_multiplier (Q a)))
    (taylorGeneratorAdjointDefect_half_negative_compatible _ KN hP)
    (fun a => A.scalar_kernel_half_negative_compatible hF0 ha0 hFlat a (Q a))
end ShrinkingSpheres
