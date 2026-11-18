import Proof.NativeTaylorGeneratorNorms
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
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- The common actual Taylor/degree/rotation generators give an order-one
commutator for arbitrary completed scalar coefficients. The bound exposes the
weighted coefficient sums needed for the two physical directions. -/
theorem closed_scalar_combination_commutator (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let G := taylorGeneratorLow (s.response.adjointHalfTaylor p)
    let Gh := taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p)
    let C0 := taylorGeneratorFixedBudget F0 ha0 C+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      (∑ a,(G a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))).comp
        (∑ b,(Gh b).comp (closedThreeJetHigherScalarMultiplierL (R b)))-
      (∑ b,(G b).comp (closedThreeJetHalfBoundaryScalarMultiplierL (R b))).comp
        (∑ a,(Gh a).comp (closedThreeJetHigherScalarMultiplierL (Q a)))=
          S.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖S‖ ≤ 3*C0^3*(∑ a,taylorGeneratorWeight (d.radius y) a*‖Q a‖)*
        (∑ b,taylorGeneratorWeight (d.radius y) b*‖R b‖) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let G := taylorGeneratorLow (s.response.adjointHalfTaylor p)
  let Gh := taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p)
  let KG := taylorGeneratorCommutator (A.domain.degreeFamily h hK (by norm_num) p).adjoint
    (fun i j => fderiv ℝ s.response.adjointHalfTaylor p (normalFrameRelativeAngularTangent d.γ p i j))
  let M := fun a => closedThreeJetHalfBoundaryScalarMultiplierL (Q a)
  let N := fun b => closedThreeJetHalfBoundaryScalarMultiplierL (R b)
  let Mh := fun a => closedThreeJetHigherScalarMultiplierL (Q a)
  let Nh := fun b => closedThreeJetHigherScalarMultiplierL (R b)
  let CM := fun b a => taylorGeneratorScalarCommutator A.scalar F0 ha0 b (Q a)
  let CN := fun a b => taylorGeneratorScalarCommutator A.scalar F0 ha0 a (R b)
  let I0 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let CB := taylorGeneratorFixedBudget F0 ha0 C
  let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let S := rightMultiplierCombinationCommutatorL G KG M N CM CN
  have hB := (taylorGeneratorFixedBudget_bounds F0 ha0 C).1
  have hCB0 : 0 ≤ CB := zero_le_one.trans hB
  have hC0 : 0 ≤ C0 := add_nonneg hCB0 (norm_nonneg _)
  have hCBC : CB ≤ C0 := le_add_of_nonneg_right (norm_nonneg _)
  have hMC : ‖closedThreeJetHalfBoundaryScalarMultiplierL‖ ≤ C0 := le_add_of_nonneg_left hCB0
  have hw (a : TaylorGeneratorIndex) : 0 ≤ taylorGeneratorWeight (d.radius y) a := by
    cases a <;> simp only [taylorGeneratorWeight] <;> positivity
  obtain ⟨hG,hKG,hScalar⟩ := A.generator_weight_bounds ha0
  refine ⟨S,?_,?_⟩
  · exact graded_finite_right_multiplier_commutator I0 G Gh KG M N Mh Nh CM CN
      (A.generator_commutator_graph hF0 he)
      (fun b a => A.scalar_commutator_graph ha0 hFlat hInv0 b (Q a))
      (fun a b => A.scalar_commutator_graph ha0 hFlat hInv0 a (R b))
      (fun a => ContinuousLinearMap.ext (fun u => closedThreeJet_higher_scalar_multiplier_half (Q a) u))
      (fun b => ContinuousLinearMap.ext (fun u => closedThreeJet_higher_scalar_multiplier_half (R b) u))
      (fun a b => closedThreeJetHigherScalarMultiplier_commute (Q a) (R b))
  · exact norm_rightMultiplierCombinationCommutatorL_of_weights G KG M N CM CN C0
      (taylorGeneratorWeight (d.radius y)) (fun a => ‖Q a‖) (fun b => ‖R b‖) hC0 hw
      (fun a => norm_nonneg _) (fun b => norm_nonneg _)
      (fun a => (hG a).trans (mul_le_mul_of_nonneg_right hCBC (hw a)))
      (fun a b => (hKG a b).trans (mul_le_mul_of_nonneg_right hCBC (mul_nonneg (hw a) (hw b))))
      (fun a => (closedThreeJetHalfBoundaryScalarMultiplierL.le_opNorm (Q a)).trans
        (mul_le_mul_of_nonneg_right hMC (norm_nonneg _)))
      (fun b => (closedThreeJetHalfBoundaryScalarMultiplierL.le_opNorm (R b)).trans
        (mul_le_mul_of_nonneg_right hMC (norm_nonneg _)))
      (fun b a => (hScalar b (Q a)).trans
        (mul_le_mul_of_nonneg_right hCBC (mul_nonneg (hw b) (norm_nonneg _))))
      (fun a b => (hScalar a (R b)).trans
        (mul_le_mul_of_nonneg_right hCBC (mul_nonneg (hw a) (norm_nonneg _))))
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
