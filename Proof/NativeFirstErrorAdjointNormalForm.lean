import Proof.LowBoundedCorrectionAdjoint
import Proof.NativeTaylorScalarAdjointNormalForm
import Proof.NativeFirstErrorScalarEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact dual-half adjoint of the complete actual native first error,
including its bounded radial correction. The unbounded generators are the
SAME ones, with signed scalar coefficients. All remaining terms are displayed
as one negative-endpoint bounded operator. -/
lemma NativeTaylorGeneratorBounds.actual_first_error_adjoint_normal_form
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (A : NativeTaylorGeneratorBounds s h hK CG)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (hr : 0 < d.radius y)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
    let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Ca j).closed p)
    let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
    let R := taylorScalarAdjointRemainderL KN
      (fun k => nativeNegativeScalarGeneratorCommutator s ha0 p k (Q k)) Q
    (s.firstAdjointHalfErrorFamily Ca p).adjoint=
      (∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp
        (closedThreeJetHalfBoundaryScalarMultiplierL (signedTaylorScalarCoefficients Q k)))+
      (R+(radialScalarBoundedHalfL ell N).adjoint).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Ca j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  have hE := (s.first_error_scalar_endpoint_realization A Ca hF0 Q0 hQ0 hr).1
  have hG := A.native_scalar_adjoint_normal_form hF0 ha0 hFlat KN hP Q
  exact low_scalar_plus_bounded_adjoint _ _ _ _ _ _ _ hE hG (radialScalarBoundedLow_adjoint ell N)
end ShrinkingSpheres
