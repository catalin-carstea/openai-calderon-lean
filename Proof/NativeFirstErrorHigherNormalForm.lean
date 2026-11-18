import Proof.GradedHigherEndpointCommutatorBound
import Proof.NativeFirstErrorAdjointNormalForm
import Proof.NativeFirstErrorAdjointEndpoints
import Proof.NativeFirstErrorAdjointRemainderNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def firstErrorHigherNormalBound
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q0 : SmoothCoefficientJets 2)
    {a b : X} {CC CH : ℝ}
    (Ca : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Cb : (k : I) → RelativeCenterErrorCoefficientFamily d y b k CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (B : ℝ) : Prop :=
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Qa := signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca)
  let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
  let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
  let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
  let low (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) := ∑ k,(Gl k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q k))
  let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) := ∑ k,(Gh k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let Nb := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cb j).closed p)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Rp := G.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN
  let Rn := nativeFirstErrorAdjointRemainderL s ha0 Q0 Ca KN
  let Zp := radialScalarBoundedHalfL ell Nb
  let Zn := radialScalarBoundedNegativeL ell Nb
  GradedHigherEndpointCommutatorBound I0 (low Qa+Rn.comp I0) (low Qb+Zn.comp I0)
    (high Qa+Rp.comp I1) (high Qb+Zp.comp I1) B

lemma firstErrorHigherNormalBound_physical
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q0 : SmoothCoefficientJets 2)
    {a b : X} {CC CH : ℝ}
    (Ca : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Cb : (k : I) → RelativeCenterErrorCoefficientFamily d y b k CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (B : ℝ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (hr : 0 < d.radius y)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (Ha Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hHb : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hb=
      (s.firstAdjointErrorFamily Cb ((y,frameVectorLinear d.frame y),0)).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hBound : G.firstErrorHigherNormalBound ha0 Q0 Ca Cb KN B) :
    GradedHigherEndpointCommutatorBound (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint
      (s.firstAdjointHalfErrorFamily Cb ((y,frameVectorLinear d.frame y),0)) Ha Hb B := by

  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Qa := signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca)
  let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
  let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
  let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
  let low (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) := ∑ k,(Gl k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q k))
  let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) := ∑ k,(Gh k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let Nb := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cb j).closed p)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Rp := G.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN
  let Rn := nativeFirstErrorAdjointRemainderL s ha0 Q0 Ca KN
  let Zp := radialScalarBoundedHalfL ell Nb
  let Zn := radialScalarBoundedNegativeL ell Nb
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have hLa := G.actual_first_error_adjoint_normal_form Ca hF0 ha0 hFlat Q0 hQ0 hr KN hP
  obtain ⟨hLb,hHB⟩ := s.first_error_scalar_endpoint_realization G Cb hF0 Q0 hQ0 hr
  have hHA := G.first_error_adjoint_balanced_pair hF0 ha0 hFlat Q0 hQ0 Ca hr KN hP
  exact hBound.congr_of_restrictions
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) hLa.symm hLb.symm
    (sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num))
    (hHa.trans hHA.symm) (hHb.trans hHB.symm)

end NativeTaylorGeneratorBounds
end ShrinkingSpheres
