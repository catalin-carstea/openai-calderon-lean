module

public import Proof.CalderonN.Chart
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proof.CalderonN.MetricDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
public import Proof.CalderonN.Coordinates

@[expose] public section

/-! Product continuation seed, ported from GreenCross in the checked 3D Theorem 3.1 release. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {n : ℕ}

/-- A smooth kernel satisfying the first equation in the first variable
and the second equation in the second variable. -/
def ProductSolutionOn (g₁ g₂ : (MetricField n)) (U : Set ((X n) × (X n))) (F : (X n) × (X n) → ℝ) : Prop :=
  ContDiffOn ℝ ∞ F U ∧
    (∀ q ∈ U, laplace g₁ (fun x => F (x, q.2)) q.1 = 0) ∧
    ∀ q ∈ U, laplace g₂ (fun y => F (q.1, y)) q.2 = 0

def initialGreenKernel (W : Set (X n)) (G₁ G₂ : (X n) × (X n) → ℝ) (q : (X n) × (X n)) : ℝ := by
  classical
  exact if q.2 ∈ W then G₁ q else G₂ q

end CalderonN
