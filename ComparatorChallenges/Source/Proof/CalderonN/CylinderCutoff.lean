module

public import Proof.CalderonN.ConformalDepth
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.FixedTube.Phase

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} {normal : I dim}
open FixedTube

@[expose] def coordinateCylinder (normal : I dim) : Set (X dim) :=
  {y | transversePair normal y y ≤ 1 ∧ -1 ≤ y normal ∧ y normal ≤ 1}

@[expose] def cylinderCore (normal : I dim) (L tb : ℝ) : Set (X dim) :=
  (coordinateCylinder normal) ∩ {y | -(1/2 : ℝ) ≤ y normal ∧ conformalDepth normal L y ≤ 2 * tb}

@[expose] def cylinderCutoff (normal : I dim) (L tb : ℝ) (y : (X dim)) : ℝ :=
  Real.smoothTransition ((y normal + 3/4) / (1/8)) *
    Real.smoothTransition ((3 * tb - conformalDepth normal L y) / (tb / 2))

end CalderonN
