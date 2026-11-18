import Proof.NativeTaylorGeneratorNorms
import Proof.FlatRaisingHigherAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- Common weighted norm for the SAME selected genuine higher generators. -/
lemma high_generator_weight_bounds (A : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (a : TaylorGeneratorIndex) :
    ‖taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num)
      ((y,frameVectorLinear d.frame y),0)) a‖ ≤
      (taylorGeneratorFixedBudget F0 ha0 CG+2)*taylorGeneratorWeight (d.radius y) a := by
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  obtain ⟨hCB,hCG,hDegree,hRot,hScalar,hAngular⟩ := taylorGeneratorFixedBudget_bounds F0 ha0 CG
  have hCGC : CG ≤ CB+2 := hCG.trans (by dsimp only [CB];linarith)
  have h2 : 2 ≤ CB+2 := by dsimp only [CB];linarith
  have hS : Real.sqrt 2 ≤ CB+2 := by dsimp only [CB];linarith [Real.sqrt_nonneg 2]
  cases a
  · exact A.high_bound.trans (mul_le_mul_of_nonneg_right hCGC (sq_nonneg _))
  · simpa only [taylorGeneratorHigh,taylorGeneratorWeight,mul_one,CB] using
      (norm_sphereSobolevShiftedDegreeL_le_two (3/2:ℝ)).trans h2
  · simpa only [taylorGeneratorHigh,taylorGeneratorWeight,mul_one,CB] using
      (norm_sphereSobolevRotationL_le (3/2:ℝ) _ _).trans hS
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
