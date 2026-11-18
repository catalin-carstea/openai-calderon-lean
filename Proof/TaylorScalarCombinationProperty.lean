import Proof.NativeTaylorScalarCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def TaylorScalarCombinationCommutes
    (P : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ph : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3) (B : ℝ) : Prop :=
  ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    (∑ a,(taylorGeneratorLow P a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))).comp
      (∑ b,(taylorGeneratorHigh Ph b).comp (closedThreeJetHigherScalarMultiplierL (R b)))-
    (∑ b,(taylorGeneratorLow P b).comp (closedThreeJetHalfBoundaryScalarMultiplierL (R b))).comp
      (∑ a,(taylorGeneratorHigh Ph a).comp (closedThreeJetHigherScalarMultiplierL (Q a)))=
      S.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧ ‖S‖ ≤ B

lemma TaylorScalarCombinationCommutes.mono
    {P : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {Ph : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    {Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3} {B B' : ℝ}
    (h : TaylorScalarCombinationCommutes P Ph Q R B) (hB : B ≤ B') :
    TaylorScalarCombinationCommutes P Ph Q R B' := by
  obtain ⟨S,hS,hN⟩ := h
  exact ⟨S,hS,hN.trans hB⟩

namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
theorem scalar_combination_commutes (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    TaylorScalarCombinationCommutes (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0))
      (A.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)) Q R
      (3*(taylorGeneratorFixedBudget F0 ha0 C+‖closedThreeJetHalfBoundaryScalarMultiplierL‖)^3*
        (∑ a,taylorGeneratorWeight (d.radius y) a*‖Q a‖)*(∑ b,taylorGeneratorWeight (d.radius y) b*‖R b‖)) :=
  A.closed_scalar_combination_commutator hF0 he ha0 hFlat hInv0 Q R
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
