module

public import Proof.CalderonN.ParametricBallConormal

import Proof.CalderonN.DilationHarmonic
import Mathlib.Tactic

/-! Adapted from `FixedBallPoissonCongruence` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem FixedBallSolution.const_mul {g : (MetricField dim)} {d b : (X dim) → ℝ}
    (hb : FixedBallSolution g d b) (a : ℝ) :
    FixedBallSolution g (fun z => a*d z) (fun z => a*b z) := by
  refine ⟨contDiff_const.mul hb.1,fun z hz => congrArg (a * ·) (hb.2.1 hz),?_⟩
  intro z hz
  rw [laplace_const_mul isOpen_univ hb.1.contDiffOn (mem_univ z) g a,hb.2.2 z hz,mul_zero]

theorem fixedBallPoisson_fderiv_eq_of_solution
    {S : Set (X dim)} (hS : IsOpen S) (hC : closedBall (0 : (X dim)) 1 ⊆ S)
    {g : (MetricField dim)} (hg : SmoothMetric S g) {d e b : (X dim) → ℝ}
    (hb : FixedBallSolution g e b) (he : EqOn d e (standardSphere dim)) :
    EqOn (fderiv ℝ (fixedBallPoisson g d)) (fderiv ℝ b) (closedBall (0 : (X dim)) 1) := by
  have hb' : FixedBallSolution g d b := ⟨hb.1,hb.2.1.trans he.symm,hb.2.2⟩
  have hex : ∃ c, FixedBallSolution g d c := ⟨b,hb'⟩
  have hP : FixedBallSolution g d (fixedBallPoisson g d) := by
    rw [fixedBallPoisson,dite_eq_left hex]
    exact Classical.choose_spec hex
  exact eqOn_fderiv_closedUnitBall hP.1 hb.1 (eqOn_fixedBallSolution hS hC hg hP hb he)

end CalderonN
