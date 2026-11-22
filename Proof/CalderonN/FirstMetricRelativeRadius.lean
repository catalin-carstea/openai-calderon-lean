module

public import Proof.CalderonN.FirstMetricNormalJets

import Proof.CalderonN.FramePullback
import Mathlib.Tactic

public section

noncomputable section

namespace CalderonN

variable {n : ℕ} [NeZero n]

/-- A change of the scalar radius is exactly a dilation of the normal coordinate
inside the unscaled reference pullback. -/
theorem framedNormalMetric_radius_mul (g : MetricField n) (e : Frame n) (E : X n × X n → X n)
    (y z : X n) (r s : ℝ) :
    framedNormalMetric g e E y (r * s) z = framedNormalMetric g e E y r (s • z) := by
  have hFrame : frameVector e y (s • z) = s • frameVector e y z := by
    rw [← frameVectorLinear_apply, ← frameVectorLinear_apply, map_smul]
  ext i j
  simp only [framedNormalMetric, normalPullbackMetricPair, hFrame, smul_smul]

/-- Relative dilation of the actual coefficient keeps the center normalization
fixed. This identity also applies for the signed radius near zero. -/
theorem normalizedFirstNormalCoeff_relativeDilation
    (d : Data n) (y z : X n) (r s : ℝ) (i j : I n) :
    normalizedFirstNormalCoeff d y (r * s) z i j =
      normalizedFirstNormalCoeff d y r (s • z) i j := by
  have hField : framedNormalMetric d.g₁ d.frame d.expMap y (r * s) =
      fun w => framedNormalMetric d.g₁ d.frame d.expMap y r (s • w) :=
    funext fun w => framedNormalMetric_radius_mul d.g₁ d.frame d.expMap y w r s
  simp only [normalizedFirstNormalCoeff, divergenceCoeff, chartVolume, hField]

end CalderonN
