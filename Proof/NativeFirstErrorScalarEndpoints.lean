import Proof.ActualFirstErrorGeneratorCommutator
import Proof.NativeTaylorGeneratorCoarseEndpoints
import Proof.RadialScalarCoarseEndpoints
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

lemma first_error_scalar_point_form
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (hr : 0 < d.radius y) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
    s.firstAdjointErrorFamily C p=
      (∑ k,(taylorGeneratorCoarse (s.response.adjointTaylor p) k).comp
        (closedOneBoundaryScalarMultiplierL (actualFirstErrorGeneratorCoefficients Q0 C k)))+
      radialScalarBoundedCoarseL (normalFrameRelativeFirstCovector d.γ d.g₁ p) N := by
  have hF := s.first_error_scalar_generator_form C Q0 hQ0 ((y,frameVectorLinear d.frame y),0)
  have hN := closedVectorNormalMultiplier_coordinate_product Q0 hQ0
    (fun j => (C j).closed ((y,frameVectorLinear d.frame y),0))
  simpa only [normalFrameRelativeInverseRadiusFactor,add_zero,inv_one,mul_one,
    inv_mul_cancel₀ hr.ne',one_smul,radialScalarBoundedCoarseL,actualFirstErrorGeneratorCoefficients,hN] using hF

lemma first_error_scalar_endpoint_realization
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (A : NativeTaylorGeneratorBounds s h hK CG)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (hr : 0 < d.radius y) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Q := actualFirstErrorGeneratorCoefficients Q0 C
    let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
    let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
    let Lo := (∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp
      (closedThreeJetHalfBoundaryScalarMultiplierL (Q k)))+
      (radialScalarBoundedNegativeL ell N).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    let Hi := (∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp
      (closedThreeJetHigherScalarMultiplierL (Q k)))+
      (radialScalarBoundedHalfL ell N).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    s.firstAdjointHalfErrorFamily C p=Lo ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      (s.firstAdjointErrorFamily C p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 C
  let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let E0 := ∑ k,(taylorGeneratorCoarse (s.response.adjointTaylor p) k).comp (closedOneBoundaryScalarMultiplierL (Q k))
  let L0 := ∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q k))
  let H0 := ∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
  let Lo := L0+(radialScalarBoundedNegativeL ell N).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
  let Hi := H0+(radialScalarBoundedHalfL ell N).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  have hE : s.firstAdjointErrorFamily C p=E0+radialScalarBoundedCoarseL ell N :=
    s.first_error_scalar_point_form C Q0 hQ0 hr
  obtain ⟨hL,hH⟩ := A.scalar_combination_coarse_endpoints hF0 Q
  obtain ⟨hZL,hZH⟩ := radialScalarBounded_coarse_endpoints ell N
  have hLo : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (s.firstAdjointErrorFamily C p)=
      Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    rw [hE,ContinuousLinearMap.comp_add]
    exact (congrArg₂ (fun U V : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => U+V) hL hZL).trans
      (ContinuousLinearMap.add_comp _ _ _).symm
  have hHi : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      (s.firstAdjointErrorFamily C p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    rw [hE,ContinuousLinearMap.add_comp]
    exact (ContinuousLinearMap.comp_add _ _ _).trans
      (congrArg₂ (fun U V : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => U+V) hH hZH)
  refine ⟨?_,hHi⟩
  exact clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) _ _
    ((s.firstAdjointHalfErrorFamily_coarse_compatible C A.domain hF0 p A.domain.pointMem).symm.trans hLo)
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
