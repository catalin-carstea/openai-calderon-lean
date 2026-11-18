import Proof.ActualFirstErrorGeneratorCommutator
import Proof.TaylorGeneratorAdjointDecomposition
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

/-- The signed generator part of the actual adjoint first error has a
quadratically gained mixed commutator with the actual unsigned generator part.
The SAME generators and scalar coefficient weighted bounds are reused. -/
theorem actual_signed_first_error_generator_commutator (A : NativeTaylorGeneratorBounds s h hK C)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a b : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Cb : (j : I) → RelativeCenterErrorCoefficientFamily d y b j CC CH) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let C0 := taylorGeneratorFixedBudget F0 ha0 C+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
    TaylorScalarCombinationCommutes (s.response.adjointHalfTaylor p)
      (A.domain.adjointHigherTaylor h hK (by norm_num) p)
      (signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca)) (actualFirstErrorGeneratorCoefficients Q0 Cb)
      ((3*C0^3*C1^2)*‖a‖*‖b‖*(d.radius y)^2) := by
  let Qa := signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca)
  let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
  let C0 := taylorGeneratorFixedBudget F0 ha0 C+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hSource := A.scalar_combination_commutes hF0 he ha0 hFlat hInv0 Qa Qb
  have hQa : (∑ k,taylorGeneratorWeight (d.radius y) k*‖Qa k‖) ≤ C1*‖a‖*(d.radius y) := by
    rw [show Qa=signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca) from rfl,
      signedTaylorScalarCoefficients_weighted_sum]
    exact hd.first_error_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC a Ca
  have hQb := hd.first_error_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC b Cb
  have hCB0 : 0 ≤ taylorGeneratorFixedBudget F0 ha0 C :=
    zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 C).1
  have hC0 : 0 ≤ C0 := add_nonneg hCB0 (norm_nonneg _)
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1)
    (by positivity)
  have hQb0 : 0 ≤ ∑ j,taylorGeneratorWeight (d.radius y) j*‖Qb j‖ := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg _ (norm_nonneg _)
    cases j <;> simp only [taylorGeneratorWeight] <;> positivity
  have hPair := mul_le_mul hQa hQb hQb0
    (show 0 ≤ C1*‖a‖*(d.radius y) from mul_nonneg (mul_nonneg hC1 (norm_nonneg _)) (hd.2.2.2.2.1.2 y hy).1.le)
  apply hSource.mono
  calc
    _ = 3*C0^3*((∑ i,taylorGeneratorWeight (d.radius y) i*‖Qa i‖)*
      (∑ j,taylorGeneratorWeight (d.radius y) j*‖Qb j‖)) := by ring
    _ ≤ 3*C0^3*((C1*‖a‖*(d.radius y))*(C1*‖b‖*(d.radius y))) :=
      mul_le_mul_of_nonneg_left hPair (by positivity)
    _ = _ := by ring
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
