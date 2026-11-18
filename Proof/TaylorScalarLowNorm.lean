import Proof.FiniteScalarRemainderNorms
import Proof.NativeTaylorGeneratorNorms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
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

lemma scalar_low_combination_norm (A : NativeTaylorGeneratorBounds s h hK C)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    ‖∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)) a).comp
      (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))‖ ≤
      (taylorGeneratorFixedBudget F0 ha0 C*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*
        (∑ a,taylorGeneratorWeight (d.radius y) a*‖Q a‖) := by
  have hCB : 0 ≤ taylorGeneratorFixedBudget F0 ha0 C :=
    zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 C).1
  exact norm_finite_scalar_combination_weighted _ closedThreeJetHalfBoundaryScalarMultiplierL Q
    (taylorGeneratorWeight (d.radius y)) _ hCB
    (fun a => by cases a <;> simp only [taylorGeneratorWeight] <;> positivity)
    (A.generator_weight_bounds ha0).1
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
