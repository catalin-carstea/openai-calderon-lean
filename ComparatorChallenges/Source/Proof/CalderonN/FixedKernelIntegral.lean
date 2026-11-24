module

public import Proof.CalderonN.Chart
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

/-! The compact domination and differentiation arguments adapt
`FixedSurfaceFluxIntegration.lean` and `FixedSurfaceTransferIntegration.lean`
from the earlier Calderón development at
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def parameterSecondOrder (a : (I dim) → (I dim) → ℝ) (b : (I dim) → ℝ) (c : ℝ)
    (f : (X dim) → ℝ) (y : (X dim)) : ℝ :=
  (∑ i, ∑ j, a i j * fderiv ℝ (fun z => fderiv ℝ f z (axis j)) y (axis i)) +
    (∑ i, b i * fderiv ℝ f y (axis i)) + c*f y

end CalderonN
