import Proof.FlatRaisingCoordinateRotation
import Proof.FlatRaisingHalfDecomposition
import Proof.NativeTaylorGeneratorCoarseEndpoints
import Proof.FirstErrorScalarCoefficientBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The right-multiplied form is exact, before the optional reordering in
`flatRaising_coordinate_rotation`. It uses the public boundary tangential
identity on which that proof also depends. -/
lemma flatRaising_right_coordinate_rotation (i : I) (u : SphereSobolev 1) :
    flatRaisingSobolevL 1 i u=
      -(∑ k : I,sphereSobolevRotationL 1 k i (coordinateMultiplierSobolevL 1 k u))+
        sphereSobolevDegreeL (coordinateMultiplierSobolevL 1 i u) := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  rw [flatRaisingSobolevL_one Q hQ,boundaryGradientAdjointL,
    coordinateBoundaryTangentialAdjoint_eq Q hQ i,oneBoundaryCoordinateMulL_eq Q hQ i]
  simp only [_root_.add_apply,_root_.neg_apply,_root_.sum_apply,ContinuousLinearMap.comp_apply]

def flatRaisingScalarCoefficients (Q0 : SmoothCoefficientJets 2) (i : I) :
    TaylorGeneratorIndex → ClosedCoefficientJets 3
  | .taylor => 0
  | .degree => smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 i)
  | .rotation k j => if j=i then -(smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k)) else 0

lemma flatRaisingScalarCoefficients_coarse_form (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (P : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i : I) :
    (∑ a,(taylorGeneratorCoarse P a).comp (closedOneBoundaryScalarMultiplierL (flatRaisingScalarCoefficients Q0 i a)))=
      flatOneRaisingL i := by
  have hCoord (k : I) : closedOneBoundaryScalarMultiplierL
      (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k))=coordinateMultiplierSobolevL 1 k := by
    rw [closedOneBoundaryScalarMultiplierL_on_smooth]
    simpa only [one_smul] using coordinateScalarSmoothJet_one_multiplier Q0 hQ0 k 1
  have hZero : closedOneBoundaryScalarMultiplierL (0 : ClosedCoefficientJets 3)=
      (0 : SphereSobolev 1 →L[ℝ] SphereSobolev 1) := closedOneBoundaryScalarMultiplierL.map_zero
  have hTaylor : (taylorGeneratorCoarse P .taylor).comp
      (closedOneBoundaryScalarMultiplierL (flatRaisingScalarCoefficients Q0 i .taylor))=0 := by
    simp only [flatRaisingScalarCoefficients,hZero,ContinuousLinearMap.comp_zero]
  have hDegree : (taylorGeneratorCoarse P .degree).comp
      (closedOneBoundaryScalarMultiplierL (flatRaisingScalarCoefficients Q0 i .degree))=
      sphereSobolevDegreeL.comp (coordinateMultiplierSobolevL 1 i) := by
    rw [flatRaisingScalarCoefficients,hCoord]
    rfl
  have hRot (k j : I) : (taylorGeneratorCoarse P (.rotation k j)).comp
      (closedOneBoundaryScalarMultiplierL (flatRaisingScalarCoefficients Q0 i (.rotation k j)))=
      if j=i then -(sphereSobolevRotationL 1 k i).comp (coordinateMultiplierSobolevL 1 k) else 0 := by
    by_cases hj : j=i
    · subst j
      simp only [flatRaisingScalarCoefficients,taylorGeneratorCoarse,ite_true,map_neg,hCoord,
        ContinuousLinearMap.comp_neg]
    · simp only [flatRaisingScalarCoefficients,ite_eq_right hj,hZero,ContinuousLinearMap.comp_zero]
  rw [taylorGeneratorIndex_sum,hTaylor,hDegree]
  simp only [zero_add,hRot,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_neg_distrib]
  apply ContinuousLinearMap.ext
  intro u
  calc
    _ = -(∑ k : I,sphereSobolevRotationL 1 k i (coordinateMultiplierSobolevL 1 k u))+
        sphereSobolevDegreeL (coordinateMultiplierSobolevL 1 i u) := by
      simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.neg_apply,_root_.sum_apply]
      abel
    _ = _ := (flatRaising_right_coordinate_rotation i u).symm

lemma flatThreeHalfRaisingL_coarse_compatible (i : I) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (flatThreeHalfRaisingL i)=
      (flatOneRaisingL i).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  have hh := flatRaisingSobolevL_inclusion (3/2:ℝ) 1 (by norm_num) i
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact hh.symm

lemma NativeTaylorGeneratorBounds.flat_raising_scalar_endpoints
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (A : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp
      (closedThreeJetHalfBoundaryScalarMultiplierL (flatRaisingScalarCoefficients Q0 i a)))=flatHalfRaisingL i ∧
    (∑ a,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) a).comp
      (closedThreeJetHigherScalarMultiplierL (flatRaisingScalarCoefficients Q0 i a)))=flatThreeHalfRaisingL i := by
  obtain ⟨hL,hH⟩ := A.scalar_combination_coarse_endpoints hF0 (flatRaisingScalarCoefficients Q0 i)
  rw [flatRaisingScalarCoefficients_coarse_form Q0 hQ0] at hL hH
  exact ⟨half_endpoint_unique_of_coarse _ _ _ hL (ContinuousLinearMap.ext (flatOneRaisingL_half i)),
    higher_endpoint_unique_of_coarse _ _ _ hH (flatThreeHalfRaisingL_coarse_compatible i)⟩
end ShrinkingSpheres
