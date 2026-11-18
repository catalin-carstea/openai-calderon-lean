import Proof.NativeTaylorGeneratorSystem
import Proof.FirstErrorScalarCoefficients
import Proof.HalfBoundaryGradientAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open Set
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma generator_coarse_endpoints (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) (a : TaylorGeneratorIndex) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (taylorGeneratorCoarse (s.response.adjointTaylor p) a)=
      (taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) a)=
      (taylorGeneratorCoarse (s.response.adjointTaylor p) a).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  cases a
  · exact ⟨A.domain.adjointHalfTaylor_coarse_compatible (by norm_num) F0 hF0 _ A.domain.pointMem,
      A.domain.adjointHigherTaylor_coarse_compatible h hK (by norm_num) F0 hF0 _ A.domain.pointMem⟩
  · exact ⟨ContinuousLinearMap.ext (fun u => sphereSobolevDegreeL_half u),sphereSobolevShiftedDegreeL_threehalf_coarse⟩
  · exact ⟨ContinuousLinearMap.ext (fun u => oneRotation_half_inclusion _ _ u),sphereSobolevRotationL_threehalf_coarse _ _⟩

lemma scalar_combination_coarse_endpoints (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let E := ∑ a,(taylorGeneratorCoarse (s.response.adjointTaylor p) a).comp (closedOneBoundaryScalarMultiplierL (Q a))
    let Lo := ∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))
    let Hi := ∑ a,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) a).comp (closedThreeJetHigherScalarMultiplierL (Q a))
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp E=
      Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      E.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,map_sum]
    apply Finset.sum_congr rfl
    intro a _
    have hh := DFunLike.congr_fun (A.generator_coarse_endpoints hF0 a).1 (closedOneBoundaryScalarMultiplierL (Q a) u)
    simpa only [ContinuousLinearMap.comp_apply,closedThreeJet_scalar_multiplier_one_half] using hh
  · apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,map_sum]
    apply Finset.sum_congr rfl
    intro a _
    have hh := DFunLike.congr_fun (A.generator_coarse_endpoints hF0 a).2 (closedThreeJetHigherScalarMultiplierL (Q a) u)
    simpa only [ContinuousLinearMap.comp_apply,closedThreeJet_higher_scalar_multiplier_one] using hh

lemma scalar_combination_balanced_pair (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (∑ a,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) a).comp
        (closedThreeJetHigherScalarMultiplierL (Q a)))=
      (∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp
        (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  balanced_endpoint_pair_of_coarse _ _ _ (A.scalar_combination_coarse_endpoints hF0 Q).1
    (A.scalar_combination_coarse_endpoints hF0 Q).2
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
