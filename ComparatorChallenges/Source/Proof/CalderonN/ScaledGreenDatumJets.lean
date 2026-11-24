module

public import Proof.CalderonN.MetricDivergence
public import Proof.CalderonN.DilationHarmonic
import Mathlib.Tactic
public import Proof.CalderonN.GreenCross
import Proof.CalderonN.Chart
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
public import Proof.CalderonN.NormalBallChart
import Proof.CalderonN.FixedKernelIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Proof.CalderonN.Coordinates

/-! Adapted from `ScaledGreenDatumJets` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev NormalGreenParameter (dim : ℕ) := ℝ × ((X dim) × ℝ)

@[expose] def normalGreenPoint (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim)) (p : (NormalGreenParameter dim))
    (z : (X dim)) : (X dim) × (X dim) :=
  (normalBallChartMap (E p.1) (e p.1) p.2.1 p.2.2 z,p.2.1)

/-- The normalized Green boundary value with radius an independent
parameter. The kernel argument stays fixed during differentiation. -/
@[expose] def scaledNormalGreenDatum (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim))
    (G : (X dim) × (X dim) → ℝ) (q : (NormalGreenParameter dim) × (X dim)) : ℝ :=
  q.1.2.2^(dim-2) * G (normalGreenPoint E e q.1 q.2)

end CalderonN
