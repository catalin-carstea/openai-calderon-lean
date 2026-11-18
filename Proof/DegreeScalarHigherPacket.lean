import Proof.NativeScalarBoundedHigherData
import Proof.DegreeScalarCoefficients
import Proof.DegreeHalfCovariantData
import Proof.FirstErrorScalarAngularCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma degree_scalar_coarse_form (P : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    (∑ a,(taylorGeneratorCoarse P a).comp (closedOneBoundaryScalarMultiplierL (degreeScalarCoefficients Q0 a)))=
      sphereSobolevDegreeL := by
  simpa only [rightScalarCombinationL_apply,taylorGeneratorCoarse] using degree_scalar_coefficients_form
    (taylorGeneratorCoarse P) closedOneBoundaryScalarMultiplierL Q0 (closedUnitCoefficient_one Q0 hQ0)

/-- The degree scalar packet agrees through its actual coarse endpoint. -/
lemma degree_scalar_endpoints (T : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp
      (closedThreeJetHalfBoundaryScalarMultiplierL (degreeScalarCoefficients Q0 a)))=degreeHalfL ∧
    (∑ a,(taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) p) a).comp
      (closedThreeJetHigherScalarMultiplierL (degreeScalarCoefficients Q0 a)))=degreeHigherL := by
  obtain ⟨hL,hH⟩ := T.scalar_combination_coarse_endpoints hF0 (degreeScalarCoefficients Q0)
  rw [degree_scalar_coarse_form _ Q0 hQ0] at hL hH
  exact ⟨half_endpoint_unique_of_coarse _ _ _ hL degreeHalfL_coarse,
    higher_endpoint_unique_of_coarse _ _ _ hH degreeHigherL_coarse⟩

/-- Degree as a SAME-generator scalar packet with zero bounded correction. -/
def degree_scalar_packet (T : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    NativeScalarBoundedEndpointData T degreeHalfL degreeHigherL (firstErrorScalarFixedBudget Q0) 0 1 := {
  coefficient := degreeScalarCoefficients Q0
  boundedHalf := 0
  boundedNegative := 0
  low_form := by
    simpa only [rightScalarCombinationL_apply,ContinuousLinearMap.zero_comp,add_zero] using
      (T.degree_scalar_endpoints hF0 Q0 hQ0).1.symm
  high_form := by
    simpa only [rightScalarCombinationL_apply,ContinuousLinearMap.zero_comp,add_zero] using
      (T.degree_scalar_endpoints hF0 Q0 hQ0).2.symm
  bounded_pair := by simp only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  coefficient_bound := by simpa only [mul_one] using degreeScalarCoefficients_weighted_bound Q0 (d.radius y)
  bounded_bounds := by simp only [norm_zero,zero_mul,le_refl,and_self] }

/-- Degree has zero angular coefficients and zero bounded higher corrections. -/
def degree_scalar_higher_packet (T : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    NativeScalarBoundedHigherData (T.degree_scalar_packet hF0 Q0 hQ0) (firstErrorScalarFixedBudget Q0) := by
  refine { angular := fun _ _ => 0
           angular_half := ?_
           augmented_bound := ?_
           boundedHigher := 0
           boundedAdjointHigher := 0
           boundedHigher_pair := ?_
           boundedAdjointHigher_pair := ?_
           higher_bounds := ?_ }
  · intro a i j
    change closedThreeJetHalfBoundaryScalarMultiplierL (0 : ClosedCoefficientJets 3)=
      closedCoefficientAngularHalfL i j (degreeScalarCoefficients Q0 a)
    cases a <;> simp only [degreeScalarCoefficients,ContinuousLinearMap.map_zero,closedUnitCoefficient_angular_half Q0 hQ0]
  · change (∑ a,taylorGeneratorWeight (d.radius y) a*(‖degreeScalarCoefficients Q0 a‖+
      ∑ _ij : I × I,‖(0 : ClosedCoefficientJets 3)‖)) ≤ firstErrorScalarFixedBudget Q0*1
    simpa only [norm_zero,Finset.sum_const_zero,add_zero,mul_one] using
      degreeScalarCoefficients_weighted_bound Q0 (d.radius y)
  · change (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp 0=
      (0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    simp only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  · change (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp 0=
      (0 : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    simp only [LinearIsometryEquiv.map_zero,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  · simp only [norm_zero,zero_mul,le_refl,and_self]
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
