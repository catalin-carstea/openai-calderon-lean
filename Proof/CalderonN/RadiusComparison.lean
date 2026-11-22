module

public import Proof.CalderonN.Radius

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Set

namespace CalderonN


/-- The comparison of the actual interpolation length with the unpowered
softplus profile. The argument adapts
`exists_referenceRadius_interpolationScale_smallness` from the earlier
Calderón formalization, revision d6704c49395a38eb07e0249afeb8ea83d67971cc. -/
private theorem exists_profile_threshold {R C : ℝ} (hR : 0 < R) (hC : 0 < C)
    {p q : ℕ} (hq : 0 < q) (hp : q + 1 ≤ p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : ℝ, 0 < u → R * u ^ p < ρ →
      C * (R * u ^ p) ^ ((1 : ℝ) / q) ≤ u / 2 := by
  let A := (2 * C) ^ q * R
  have hA : 0 < A := by dsimp [A]; positivity
  let u₀ := 1 / (1 + A)
  have hu₀ : 0 < u₀ := by dsimp [u₀]; positivity
  have hden : 0 < 1 + A := by positivity
  have hu₀one : u₀ ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  have hAu₀ : A * u₀ ≤ 1 := by
    dsimp [u₀]
    rw [mul_one_div]
    exact (div_le_iff₀ hden).mpr (by linarith)
  refine ⟨R * u₀ ^ p, mul_pos hR (pow_pos hu₀ _), ?_⟩
  intro u hu hr
  have hsmall : u < u₀ :=
    lt_of_pow_lt_pow_left₀ p hu₀.le (lt_of_mul_lt_mul_left hr hR.le)
  have huOne := hsmall.le.trans hu₀one
  have hAu := (mul_le_mul_of_nonneg_left hsmall.le hA.le).trans hAu₀
  have hPower : A * u ^ p ≤ u ^ q := by
    calc
      _ ≤ A * u ^ (q+1) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hu.le huOne hp) hA.le
      _ = (u ^ q) * (A * u) := by rw [pow_succ]; ring
      _ ≤ u ^ q := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hAu (pow_nonneg hu.le _)
  let r := R * u ^ p
  have hroot : (r ^ ((1 : ℝ) / q)) ^ q = r := by
    have hrpos : 0 < r := mul_pos hR (pow_pos hu _)
    simpa using Real.rpow_inv_natCast_pow hrpos.le hq.ne'
  have hpow : (2 * C * r ^ ((1 : ℝ) / q)) ^ q ≤ u ^ q := by
    rw [mul_pow, hroot]
    simpa only [A, r, mul_assoc] using hPower
  have h₁ := le_of_pow_le_pow_left₀ hq.ne' hu.le hpow
  linarith

/-- On a ball of radius r(y)^(1/q) around a sufficiently small sphere,
the original radius is comparable at the two centers with fixed constants. -/
theorem exists_radius_comparison_on_interpolation_balls
    {E : Type*} [MetricSpace E] {Y : Set E} {depth : E → ℝ} {L : NNReal}
    (hdepth : LipschitzOnWith L depth Y) {R : ℝ} (hR : 0 < R) {p q : ℕ} (hq : 0 < q) (hp : q + 1 ≤ p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ δ : ℝ, 0 < δ → ∀ y ∈ Y,
      let r := shrinkingRadius R p depth δ y
      r < ρ → ∀ z ∈ Y, dist z y ≤ r ^ ((1 : ℝ) / q) →
        (1 / 2 : ℝ) ^ p * r ≤ shrinkingRadius R p depth δ z ∧
          shrinkingRadius R p depth δ z ≤ (3 / 2 : ℝ) ^ p * r := by
  obtain ⟨ρ, hρ, hsmall⟩ := exists_profile_threshold (C := (L : ℝ) + 1)
    hR (by positivity) hq hp
  refine ⟨ρ, hρ, ?_⟩
  intro δ hδ y hy
  dsimp only
  intro hr z hz hdist
  let u := softplus δ (depth y)
  let v := softplus δ (depth z)
  have hu : 0 < u := softplus_pos hδ _
  have hv : 0 < v := softplus_pos hδ _
  have hctrl : |v - u| ≤ u / 2 := by
    calc
      _ ≤ (L : ℝ) * dist z y := by
        have hs := (lipschitzWith_softplus hδ.ne').dist_le_mul (depth z) (depth y)
        rw [NNReal.coe_one, one_mul, Real.dist_eq] at hs
        exact hs.trans (hdepth.dist_le_mul z hz y hy)
      _ ≤ ((L : ℝ) + 1) * dist z y :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ ≤ ((L : ℝ) + 1) * (R * u ^ p) ^ ((1 : ℝ) / q) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ ≤ _ := hsmall u hu hr
  have hlo : (1 / 2 : ℝ) * u ≤ v := by linarith [(abs_le.mp hctrl).1]
  have hhi : v ≤ (3 / 2 : ℝ) * u := by linarith [(abs_le.mp hctrl).2]
  change (1 / 2 : ℝ) ^ p * (R * u ^ p) ≤ R * v ^ p ∧
    R * v ^ p ≤ (3 / 2 : ℝ) ^ p * (R * u ^ p)
  constructor
  · calc
      _ = R * ((1 / 2 : ℝ) * u) ^ p := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlo p) hR.le
  · calc
      _ ≤ R * ((3 / 2 : ℝ) * u) ^ p := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hv.le hhi p) hR.le
      _ = _ := by rw [mul_pow]; ring

end CalderonN
