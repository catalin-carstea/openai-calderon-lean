import Proof.NativeHigherScalarCombinationData
import Proof.GradedHigherEndpointCommutatorBound
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
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS BG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- General genuinely graded scalar-generator commutator, preserving
SEPARATE scales for mixed degree/raising/error applications. The angular
coefficient witnesses are explicit and no higher norm is inferred from a
lower Sobolev realization. -/
lemma higher_scalar_combination_bound
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (HS : NativeScalarGeneratorRotationData A ha0 BS) (HG : NativeHigherGeneratorCommutatorData G BG)
    (hΩ : IsOpen Ω) (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (AQ AR : TaylorGeneratorIndex → I × I → ClosedCoefficientJets 3)
    (hAQ : ∀ a i j,closedThreeJetHalfBoundaryScalarMultiplierL (AQ a (i,j))=closedCoefficientAngularHalfL i j (Q a))
    (hAR : ∀ b i j,closedThreeJetHalfBoundaryScalarMultiplierL (AR b (i,j))=closedCoefficientAngularHalfL i j (R b))
    (CB scaleA scaleB : ℝ) (hCB : 0 ≤ CB) (hScaleA : 0 ≤ scaleA) (hScaleB : 0 ≤ scaleB)
    (hQ : (∑ a,taylorGeneratorWeight (d.radius y) a*(‖Q a‖+∑ ij : I × I,‖AQ a ij‖)) ≤ CB*scaleA)
    (hR : (∑ a,taylorGeneratorWeight (d.radius y) a*(‖R a‖+∑ ij : I × I,‖AR a ij‖)) ≤ CB*scaleB) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
    let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
    let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
    GradedHigherEndpointCommutatorBound (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (∑ a,(Gl a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a)))
      (∑ b,(Gl b).comp (closedThreeJetHalfBoundaryScalarMultiplierL (R b)))
      (∑ a,(Gh a).comp (closedThreeJetHigherScalarMultiplierL (Q a)))
      (∑ b,(Gh b).comp (closedThreeJetHigherScalarMultiplierL (R b)))
      ((3*C^3*CB^2)*scaleA*scaleB) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
  have hC : 0 ≤ C := by
    have hGen := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
    dsimp only [C]
    positivity
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have hGraph := A.scalarCombinationHigherFamily_graph G ha0 HS hΩ hF0 he hFlat s.point.flatStrong
    (fun a _ => Q a) (fun b _ => R b) (fun a ij _ => AQ a ij) (fun b ij _ => AR b ij) hAQ hAR
  have hNorm := A.scalarCombinationHigherFamily_norm_le G ha0 HS HG
    (fun a _ => Q a) (fun b _ => R b) (fun a ij _ => AQ a ij) (fun b ij _ => AR b ij)
  have hProduct := mul_le_mul hQ hR
    (show 0 ≤ ∑ a,taylorGeneratorWeight (d.radius y) a*(‖R a‖+∑ ij : I × I,‖AR a ij‖) from by
      apply Finset.sum_nonneg
      intro a _
      have hw : 0 ≤ taylorGeneratorWeight (d.radius y) a := by cases a <;> simp only [taylorGeneratorWeight] <;> positivity
      exact mul_nonneg hw (add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))))
    (mul_nonneg hCB hScaleA)
  refine ⟨A.scalarCombinationHigherFamily G ha0 (fun a _ => Q a) (fun b _ => R b)
    (fun a ij _ => AQ a ij) (fun b ij _ => AR b ij) p,hGraph,?_⟩
  calc
    _ ≤ 3*C^3*(∑ a,taylorGeneratorWeight (d.radius y) a*(‖Q a‖+∑ ij : I × I,‖AQ a ij‖))*
      (∑ b,taylorGeneratorWeight (d.radius y) b*(‖R b‖+∑ ij : I × I,‖AR b ij‖)) := hNorm
    _ = 3*C^3*((∑ a,taylorGeneratorWeight (d.radius y) a*(‖Q a‖+∑ ij : I × I,‖AQ a ij‖))*
      (∑ b,taylorGeneratorWeight (d.radius y) b*(‖R b‖+∑ ij : I × I,‖AR b ij‖))) := by ring
    _ ≤ 3*C^3*((CB*scaleA)*(CB*scaleB)) :=
      mul_le_mul_of_nonneg_left hProduct (show 0 ≤ 3*C^3 by positivity)
    _ = _ := by ring
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
