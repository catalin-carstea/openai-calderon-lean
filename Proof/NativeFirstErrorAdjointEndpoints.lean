import Proof.TaylorScalarAdjointRemainderEndpoints
import Proof.NativeTaylorGeneratorCoarseEndpoints
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

lemma bounded_endpoint_adjoints_compatible {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (I0 Zp Zn : E →L[ℝ] E) (hI : I0.adjoint=I0)
    (hZ : I0.comp Zp=Zn.comp I0) : I0.comp Zn.adjoint=Zp.adjoint.comp I0 := by
  have hh := congrArg (fun T : E →L[ℝ] E => T.adjoint) hZ
  simpa only [ContinuousLinearMap.adjoint_comp,hI] using hh.symm

namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def firstErrorAdjointRemainderHalfL (A : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  taylorScalarAdjointRemainderHalfL KN (fun k => taylorGeneratorScalarCommutator A.scalar F0 ha0 k (Q k)) Q+
    (radialScalarBoundedNegativeL (normalFrameRelativeFirstCovector d.γ d.g₁ p)
      (∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Ca j).closed p))).adjoint

lemma first_error_adjoint_remainder_half_negative_compatible (A : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2) (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN)=
      (nativeFirstErrorAdjointRemainderL s ha0 Q0 Ca KN).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Ca j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  have hS := A.scalar_adjoint_remainder_half_negative_compatible hF0 ha0 hFlat KN hP Q
  have hZ := bounded_endpoint_adjoints_compatible _ (radialScalarBoundedHalfL ell N)
    (radialScalarBoundedNegativeL ell N) sphereSobolevHalfNegativeInclusion_adjoint
    (radialScalarBounded_half_negative_compatible ell N)
  exact (ContinuousLinearMap.comp_add _ _ _).trans
    ((congrArg₂ (fun U V : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => U+V) hS hZ).trans
      (ContinuousLinearMap.add_comp _ _ _).symm)

def firstErrorAdjointHigherL (A : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  (∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp
    (closedThreeJetHigherScalarMultiplierL (signedTaylorScalarCoefficients Q k)))+
    (A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

lemma first_error_adjoint_balanced_pair (A : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH) (hr : 0 < d.radius y)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (A.firstErrorAdjointHigherL ha0 Q0 Ca KN)=
      (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  have hG := A.scalar_combination_balanced_pair hF0 (signedTaylorScalarCoefficients Q)
  have hR := A.first_error_adjoint_remainder_half_negative_compatible hF0 ha0 hFlat Q0 Ca KN hP
  have hE := A.actual_first_error_adjoint_normal_form Ca hF0 ha0 hFlat Q0 hQ0 hr KN hP
  have hR' := (ContinuousLinearMap.comp_assoc
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))).symm.trans
      (congrArg (fun T => T.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) hR)
  change _ = _
  rw [hE,ContinuousLinearMap.add_comp]
  exact (ContinuousLinearMap.comp_add _ _ _).trans
    ((congrArg₂ (fun U V : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => U+V)
      hG hR').trans
        (by rfl))
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
