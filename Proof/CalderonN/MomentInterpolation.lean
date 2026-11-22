module

public import Proof.CalderonN.Coercivity
public import Proof.CalderonN.Radius
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

import Proof.CalderonN.RadiusComparison
import Proof.CalderonN.FiniteInterpolation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- On a cutoff plateau, an upper bound for the radius on the entire
interpolation ball turns the weighted moment into a local L² bound. -/
theorem localLpNorm_le_weighted_moment
    {Y : Set (X dim)} {μ : Measure (X dim)} {V χ r : (X dim) → ℝ} {y : (X dim)} {s b : ℝ}
    (hV : ContinuousOn V Y) (hsub : ball y s ⊆ Y) (hχ : ∀ z ∈ ball y s, χ z = 1)
    (hr : ∀ z ∈ ball y s, 0 < r z ∧ r z ≤ b) :
    eLpNorm V 2 (μ.restrict (ball y s)) ≤
      ENNReal.ofReal (b ^ 2) * eLpNorm (fun z => χ z * V z / (r z) ^ 2) 2 (μ.restrict Y) := by
  have hpoint : ∀ᵐ z ∂μ.restrict (ball y s),
      ‖V z‖ ≤ b ^ 2 * ‖χ z * V z / (r z) ^ 2‖ := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    obtain ⟨hrz, hzle⟩ := hr z hz
    have hratio : ‖χ z * V z / (r z) ^ 2‖ = ‖V z‖ / (r z) ^ 2 := by
      simp only [hχ z hz, one_mul, norm_div, Real.norm_eq_abs, abs_of_pos (pow_pos hrz 2)]
    calc
      _ = (r z) ^ 2 * (‖V z‖ / (r z) ^ 2) := by field_simp [hrz.ne']
      _ ≤ b ^ 2 * (‖V z‖ / (r z) ^ 2) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hrz.le hzle 2) (div_nonneg (norm_nonneg _) (sq_nonneg _))
      _ = _ := by rw [hratio]
  have hlocal := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((hV.mono hsub).aestronglyMeasurable (μ := μ) isOpen_ball.measurableSet) hpoint (2 : ℝ≥0∞)
  exact hlocal.trans (mul_le_mul_of_nonneg_left
    (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)) (by positivity))

/-- Quantitative Section 6.2 inference on one physical chart. The cutoff
and weighted moment use the same radius as the interpolation scale. -/
theorem exists_three_halves_jet_of_weighted_moment
    {Y : Set (X dim)}
    {depth : (X dim) → ℝ} {L : NNReal} (hdepth : LipschitzOnWith L depth Y)
    {R : ℝ} (hR : 0 < R) {p : ℕ} (hp : 21 + dim ≤ p) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧
      ∀ (Ω : Set (X dim)), IsOpen Ω → Y ⊆ Ω → ∀ (V χ : (X dim) → ℝ), ContDiffOn ℝ ∞ V Ω →
      ∀ (δ : ℝ), 0 < δ → ∀ y ∈ Y, ∀ A M : ℝ, 0 ≤ A → 0 ≤ M →
        let r := shrinkingRadius R p depth δ y
        let s := r ^ ((1 : ℝ) / (20 + (dim : ℝ)))
        r < ρ → r ≤ 1 →
        ball y s ⊆ Y → closedBall y s ⊆ Ω →
        (∀ z ∈ ball y s, χ z = 1) →
        (∀ z ∈ closedBall y s, ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) V z‖ ≤ M) →
        eLpNorm (fun z => χ z * V z / (shrinkingRadius R p depth δ z) ^ 2) 2
          (volume.restrict Y) ≤ ENNReal.ofReal A →
        ∀ j : ℕ, j ≤ 10 →
          ‖iteratedFDeriv ℝ j V y‖ ≤
            C * ((((3 / 2 : ℝ) ^ p) ^ 2) * A + M) * r ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hinterp⟩ := exists_uniform_taylor_jet_le_three_halves_of_local_L2_bound (dim := dim)
  obtain ⟨ρ, hρ, hcompare⟩ := exists_radius_comparison_on_interpolation_balls hdepth hR (p := p) (q := 20 + dim) (by omega) (by omega)
  refine ⟨C, ρ, hC, hρ, ?_⟩
  intro Ω hΩ hYΩ V χ hV δ hδ y hy A M hA hM
  dsimp only
  intro hrsmall hrOne hY hclosed hχ h45 hmoment j hj
  let radii := shrinkingRadius R p depth δ
  let r := radii y
  let s := r ^ ((1 : ℝ) / (20 + (dim : ℝ)))
  let B := (3 / 2 : ℝ) ^ p
  have hr : 0 < r := shrinkingRadius_pos hR hδ p depth y
  have hlocal := localLpNorm_le_weighted_moment
    (μ := volume) (b := B * r) (r := radii) (hV.continuousOn.mono hYΩ) hY hχ (by
      intro z hz
      exact ⟨shrinkingRadius_pos hR hδ p depth z,
        (hcompare δ hδ y hy hrsmall z (hY hz) (by simpa using (mem_ball.mp hz).le)).2⟩)
  have hENN : eLpNorm V 2 (volume.restrict (ball y s)) ≤ ENNReal.ofReal ((B * r) ^ 2) *
      ENNReal.ofReal A :=
    hlocal.trans (mul_le_mul_of_nonneg_left hmoment (by positivity))
  have hreal : (eLpNorm V 2 (volume.restrict (ball y s))).toReal ≤ (B ^ 2 * A) * r ^ 2 := by
    calc
      _ ≤ (ENNReal.ofReal ((B * r) ^ 2) * ENNReal.ofReal A).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hENN
      _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal hA]
        ring
  exact hinterp V Ω y r (B ^ 2 * A) M j hΩ hV (hYΩ hy) hr hrOne (by positivity) hM
    hclosed h45 hreal hj

end CalderonN
