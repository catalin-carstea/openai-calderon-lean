import Proof.FiniteScalarRemainderNorms
import Proof.NativeHigherGeneratorNorms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma scalar_high_combination_norm (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    ‖∑ a,(taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num)
      ((y,frameVectorLinear d.frame y),0)) a).comp (closedThreeJetHigherScalarMultiplierL (Q a))‖ ≤
      ((taylorGeneratorFixedBudget F0 ha0 CG+2)*‖closedThreeJetHigherScalarMultiplierL‖)*
        (∑ a,taylorGeneratorWeight (d.radius y) a*‖Q a‖) := by
  have hCB : 0 ≤ taylorGeneratorFixedBudget F0 ha0 CG+2 := by
    have hh := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
    linarith
  exact norm_finite_scalar_combination_weighted _ closedThreeJetHigherScalarMultiplierL Q
    (taylorGeneratorWeight (d.radius y)) _ hCB
    (fun a => by cases a <;> simp only [taylorGeneratorWeight] <;> positivity)
    (G.high_generator_weight_bounds ha0)
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
