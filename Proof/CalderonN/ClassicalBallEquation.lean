module

public import Proof.CalderonN.ClassicalBallBoundaryValue

public import Proof.CalderonN.ClassicalSourceEquation
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Gradient InnerProductSpace Distributions Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim]


open CalderonN.BallDirichlet

set_option maxHeartbeats 1400000 in
/-- The equation solved by the weak inverse becomes the pointwise
divergence equation for its ambient smooth representative. -/
theorem negativeBallDivergence_eq_of_ballWeakSolution
    {a : (X dim) → (Mat dim)} (ha : ContDiff ℝ ∞ a) {f u : (X dim) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (v : (FixedBallH1Zero dim)) (hV : TauCeti.W1p.value (v : (FixedBallH1 dim))
       =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] u)
    (F : Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)))
    (hF : ⇑F =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] f)
    (h : TauCeti.PDE.IsWeakSolutionDirichlet a 0 0 F v) :
    EqOn (negativeBallDivergence a u) f (ball (0 : (X dim)) 1) :=
  negativeBallDivergence_eq_of_interior_representation
    (U := fixedBallOpens dim) le_rfl ha hf hu v hV F hF h

end CalderonN
