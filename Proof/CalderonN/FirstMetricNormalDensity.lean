module

public import Proof.CalderonN.FirstMetricConformalDepth
public import Proof.CalderonN.FramedNormalMetric
public import Proof.CalderonN.NormalDivergenceScale

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {n : ℕ} [NeZero n]

/-- The positive square root of the first metric's conformal factor. -/
def firstMetricScale (γ g₁ : MetricField n) (x : X n) : ℝ :=
  Real.exp (-firstMetricConformalDepth γ g₁ x)

/-- The conformal scalar in the actual first metric's divergence coefficient. -/
def firstMetricDensityFactor (γ g₁ : MetricField n) (x : X n) : ℝ :=
  firstMetricScale γ g₁ x ^ (n-2)

theorem firstMetricScale_pos (γ g₁ : MetricField n) (x : X n) :
    0 < firstMetricScale γ g₁ x := Real.exp_pos _

theorem firstMetricDensityFactor_pos (γ g₁ : MetricField n) (x : X n) :
    0 < firstMetricDensityFactor γ g₁ x := pow_pos (firstMetricScale_pos γ g₁ x) (n-2)

theorem Background.firstMetricScale_sq {Ω : Set (X n)} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField n} {e : Frame n}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X n} (hx : x ∈ Ω) :
    (firstMetricScale γ g₁ x)^2 = firstMetricConformalFactor γ g₁ x := by
  rw [hB.firstMetricConformalFactor_eq_exp_depth hK hx, firstMetricScale, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem Background.firstMetricDensityFactor_smooth {Ω : Set (X n)} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField n} {e : Frame n}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (firstMetricDensityFactor γ g₁) Ω :=
  (hB.firstMetricConformalDepth_smooth hK).neg.exp.pow _

/-- The conformal density of the actual first metric in the signed rescaled normal map. -/
def framedFirstDensityFactor (d : Data n) (y : X n) (s : ℝ) (z : X n) : ℝ :=
  firstMetricDensityFactor d.γ d.g₁ (d.expMap (y,s • frameVector d.frame y z))

theorem Background.framed_firstMetric_scale {Ω : Set (X n)} {m : ℕ}
    {K : ℝ} {M : Fin (m+1) → ℝ} {d : Data n} {e : Frame n}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ e) (hK : 0 < K)
    {y z : X n} {s : ℝ} (hx : d.expMap (y,s • frameVector d.frame y z) ∈ Ω) :
    framedNormalMetric d.g₁ d.frame d.expMap y s z =
      (firstMetricScale d.γ d.g₁ (d.expMap (y,s • frameVector d.frame y z)))^2 •
        framedNormalMetric d.γ d.frame d.expMap y s z := by
  ext i j
  change metricPair d.g₁ _ _ _ = _
  rw [hB.firstMetricPair_eq_conformalFactor hK hx, ← hB.firstMetricScale_sq hK hx]
  rfl

/-- Exact all-dimensional density factorization in the same normal chart used
    to pull back the first-metric Dirichlet equation. -/
theorem Background.framed_firstMetric_density_coefficient (hn : 2 ≤ n)
    {Ω : Set (X n)} {m : ℕ} {K : ℝ} {M : Fin (m+1) → ℝ} {d : Data n} {e : Frame n}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ e) (hK : 0 < K)
    {y z : X n} {s : ℝ} (hx : d.expMap (y,s • frameVector d.frame y z) ∈ Ω)
    (hDet : IsUnit (framedNormalMetric d.γ d.frame d.expMap y s z).det) (i j : I n) :
    divergenceCoeff (framedNormalMetric d.g₁ d.frame d.expMap y s) z i j =
      framedFirstDensityFactor d y s z *
        divergenceCoeff (framedNormalMetric d.γ d.frame d.expMap y s) z i j := by
  let r := firstMetricScale d.γ d.g₁ (d.expMap (y,s • frameVector d.frame y z))
  let g := framedNormalMetric d.γ d.frame d.expMap y s
  calc
    _ = divergenceCoeff (fun w => r^2 • g w) z i j := by
      simp only [divergenceCoeff, chartVolume, hB.framed_firstMetric_scale hK hx, r, g]
    _ = _ := divergenceCoeff_scale_sq hn g r (firstMetricScale_pos _ _ _) z hDet i j

end CalderonN
