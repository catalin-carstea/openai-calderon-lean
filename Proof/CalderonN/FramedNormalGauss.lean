module

public import Proof.CalderonN.NormalGaussPullback
public import Proof.CalderonN.FramedNormalMetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]
lemma NormalCoordinates.framedNormalMetric_gauss {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : (Frame dim)) (r : ℝ) (hr : r ≠ 0) (z u : (X dim))
    (hv : r • frameVector e y z ∈ interior (disk g y (R y))) :
    metricPair (framedNormalMetric g e expMap y r) z z u =
      metricPair g y (frameVector e y z) (frameVector e y u) := by
  have hG := hN.gauss_vertical hΩ hg hK hy hyΩ
    (r • frameVector e y z) (frameVector e y u) hv
  rw [map_smul,metricPair_smul_left,metricPair_smul_left] at hG
  have hh := mul_left_cancel₀ hr hG
  rw [framedNormalMetric_pair]
  exact hh
end CalderonN
