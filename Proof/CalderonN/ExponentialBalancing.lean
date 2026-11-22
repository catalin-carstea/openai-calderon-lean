module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic

@[expose] public section

/-! The exponential balancing proof is adopted from `MixedKernelConstructionC3SupportV015`
at anisotropic-calderon-lean revision `d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

open Filter
open scoped Topology

namespace CalderonN.Elliptic

/-- G1(d): exponential balancing. If `A <= D` and for every `tau >= tau0`
`A <= C (exp(-a tau) D + exp(b tau) S)`, then
`A <= (2C + exp(a tau0)) S^(a/(a+b)) D^(b/(a+b))`. All cases `S = 0`, `D = 0` included. -/
theorem exp_balance {a b C τ0 A S D : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hAD : A ≤ D)
    (h : ∀ τ : ℝ, τ0 ≤ τ → A ≤ C * (Real.exp (-(a * τ)) * D + Real.exp (b * τ) * S)) :
    A ≤ (2 * C + Real.exp (a * τ0)) * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by
  have hab : 0 < a + b := add_pos ha hb
  have hD : 0 ≤ D := hA.trans hAD
  have hK : 0 ≤ 2 * C + Real.exp (a * τ0) := by positivity
  have hRHS : 0 ≤ (2 * C + Real.exp (a * τ0)) * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by
    positivity
  rcases hD.eq_or_lt with hD0 | hDpos
  · subst hD0
    linarith
  rcases hS.eq_or_lt with hS0 | hSpos
  · subst hS0
    have hlim : Tendsto (fun τ : ℝ => C * (Real.exp (-(a * τ)) * D + Real.exp (b * τ) * 0))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun τ : ℝ => Real.exp (-(a * τ))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (Filter.Tendsto.const_mul_atTop ha tendsto_id)
      have h2 := (h1.mul_const D).const_mul C
      simpa using h2
    have hA0 : A ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨τ0, h⟩)
    linarith
  -- both positive
  have hSne : S ≠ 0 := hSpos.ne'
  have hDne : D ≠ 0 := hDpos.ne'
  have hX : S ^ (a / (a + b)) * D ^ (b / (a + b)) =
      Real.exp (Real.log S * (a / (a + b)) + Real.log D * (b / (a + b))) := by
    rw [Real.rpow_def_of_pos hSpos, Real.rpow_def_of_pos hDpos, ← Real.exp_add]
  have hXpos : 0 ≤ S ^ (a / (a + b)) * D ^ (b / (a + b)) := by positivity
  set t : ℝ := Real.log (D / S) / (a + b) with ht_def
  have hlogDS : Real.log (D / S) = Real.log D - Real.log S := Real.log_div hDne hSne
  by_cases ht : τ0 ≤ t
  · have h1 := h t ht
    have e1 : Real.exp (-(a * t)) * D = S ^ (a / (a + b)) * D ^ (b / (a + b)) := by
      rw [hX, ← Real.exp_log hDpos, ← Real.exp_add, Real.log_exp]
      congr 1
      rw [ht_def, hlogDS]
      field_simp
      ring
    have e2 : Real.exp (b * t) * S = S ^ (a / (a + b)) * D ^ (b / (a + b)) := by
      rw [hX]
      conv_lhs => rw [← Real.exp_log hSpos]
      rw [← Real.exp_add]
      congr 1
      rw [ht_def, hlogDS]
      field_simp
      ring
    rw [e1, e2] at h1
    have hexp : 0 ≤ Real.exp (a * τ0) * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by
      positivity
    nlinarith
  · push Not at ht
    -- below the threshold: `D < exp((a+b) tau0) S`
    have hlt : Real.log D < (a + b) * τ0 + Real.log S := by
      have : Real.log (D / S) < (a + b) * τ0 := by
        rw [ht_def] at ht
        have := (div_lt_iff₀ hab).1 ht
        linarith
      linarith
    have hDexp : D = Real.exp (Real.log D * (a / (a + b)) + Real.log D * (b / (a + b))) := by
      rw [← mul_add, ← add_div, div_self hab.ne', mul_one, Real.exp_log hDpos]
    have hga : 0 < a / (a + b) := div_pos ha hab
    have hle : D ≤ Real.exp (a * τ0) * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by
      rw [hX, ← Real.exp_add]
      conv_lhs => rw [hDexp]
      apply Real.exp_le_exp.2
      have h3 : Real.log D * (a / (a + b)) ≤ ((a + b) * τ0 + Real.log S) * (a / (a + b)) :=
        mul_le_mul_of_nonneg_right hlt.le hga.le
      have h4 : ((a + b) * τ0 + Real.log S) * (a / (a + b)) =
          a * τ0 + Real.log S * (a / (a + b)) := by
        field_simp
      linarith
    have h2C : 0 ≤ 2 * C * (S ^ (a / (a + b)) * D ^ (b / (a + b))) := by positivity
    nlinarith
/-- The source concave height profile `phi(s) = s - kappa s^2`. -/
@[expose] def strictHeight (κ s : ℝ) : ℝ := s - κ * s ^ 2

/-- G1(e): positivity of the bottom gap and the denominator for the source levels
`-l+3e < -e < l+3e`, under the source smallness `kappa l <= 1/4`, `4e < kappa l^2`. -/
theorem strictHeight_gaps {κ l e : ℝ} (hκ : 0 < κ) (hl : 0 < l) (hκl : κ * l ≤ 1 / 4)
    (he : 0 ≤ e) (he4 : 4 * e < κ * l ^ 2) :
    κ * e < 1 / 64 ∧
    strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e) = 2 * l * (1 - 6 * (κ * e)) ∧
    2 * (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) -
        (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) =
      2 * κ * l ^ 2 - 8 * e + 16 * κ * e ^ 2 ∧
    (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) -
        (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) =
      l - κ * l * l - 6 * (l * (κ * e)) - 8 * (e * (κ * e)) + 4 * e := by
  have hκl0 : 0 < κ * l := mul_pos hκ hl
  have hsq : κ * l * (κ * l) ≤ κ * l * (1 / 4) := mul_le_mul_of_nonneg_left hκl hκl0.le
  have h4 : κ * (4 * e) < κ * (κ * l ^ 2) := mul_lt_mul_of_pos_left he4 hκ
  refine ⟨by nlinarith, ?_, ?_, ?_⟩ <;> · unfold strictHeight; ring

/-- G1(e): the source exponent (cross:exponent) lies strictly between `1/2` and `1`. -/
theorem strictExponent_bounds {κ l e : ℝ} (hκ : 0 < κ) (hl : 0 < l) (hκl : κ * l ≤ 1 / 4)
    (he : 0 ≤ e) (he4 : 4 * e < κ * l ^ 2) :
    0 < strictHeight κ (-e) - strictHeight κ (-l + 3 * e) ∧
    0 < strictHeight κ (l + 3 * e) - strictHeight κ (-e) ∧
    1 / 2 < (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
        (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) ∧
    (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
        (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) < 1 := by
  obtain ⟨h1, hDn, h2N, hDN⟩ := strictHeight_gaps hκ hl hκl he he4
  have hl1 : κ * l * l ≤ 1 / 4 * l := mul_le_mul_of_nonneg_right hκl hl.le
  have hl2 : l * (κ * e) < l * (1 / 64) := mul_lt_mul_of_pos_left h1 hl
  have hl3 : e * (κ * e) ≤ e * (1 / 64) := mul_le_mul_of_nonneg_left h1.le he
  have hDpos : 0 < strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e) := by
    rw [hDn]; nlinarith
  have hkee : 0 ≤ κ * e ^ 2 := by positivity
  have hgap : 0 < l - κ * l * l - 6 * (l * (κ * e)) - 8 * (e * (κ * e)) + 4 * e := by
    nlinarith
  have hN : 0 < strictHeight κ (-e) - strictHeight κ (-l + 3 * e) := by nlinarith
  refine ⟨hN, ?_, ?_, ?_⟩
  · have : strictHeight κ (l + 3 * e) - strictHeight κ (-e) =
        (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)) -
          (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) := by ring
    rw [this, hDN]; exact hgap
  · rw [lt_div_iff₀ hDpos]; nlinarith
  · rw [div_lt_one hDpos]; nlinarith


/-- W1: the weighted SQUARED inequality gives the unsquared one (τ ≥ 1). -/
theorem weighted_sq_to_unsq {τ c a b C A D S : ℝ} (hτ : 1 ≤ τ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hD : 0 ≤ D) (hS : 0 ≤ S)
    (h : τ ^ 3 * (Real.exp (2 * (τ * c)) * A ^ 2) ≤
      C * (Real.exp (2 * (τ * a)) * D ^ 2 + Real.exp (2 * (τ * b)) * S ^ 2)) :
    Real.exp (τ * c) * A ≤ Real.sqrt C * (Real.exp (τ * a) * D + Real.exp (τ * b) * S) := by
  have hsq : ∀ t : ℝ, Real.exp (2 * t) = Real.exp t ^ 2 := fun t => by
    rw [sq, ← Real.exp_add, two_mul]
  rw [hsq, hsq, hsq] at h
  have hX : 0 ≤ Real.exp (τ * c) * A := mul_nonneg (Real.exp_pos _).le hA
  have hY : 0 ≤ Real.exp (τ * a) * D := mul_nonneg (Real.exp_pos _).le hD
  have hZ : 0 ≤ Real.exp (τ * b) * S := mul_nonneg (Real.exp_pos _).le hS
  have hτ3 : 1 ≤ τ ^ 3 := one_le_pow₀ hτ
  have hnn : 0 ≤ Real.exp (τ * c) ^ 2 * A ^ 2 := by positivity
  have h1 : (Real.exp (τ * c) * A) ^ 2 ≤
      C * ((Real.exp (τ * a) * D) ^ 2 + (Real.exp (τ * b) * S) ^ 2) :=
    calc (Real.exp (τ * c) * A) ^ 2 = Real.exp (τ * c) ^ 2 * A ^ 2 := by ring
      _ ≤ τ ^ 3 * (Real.exp (τ * c) ^ 2 * A ^ 2) := le_mul_of_one_le_left hnn hτ3
      _ ≤ _ := h
      _ = _ := by ring
  have h2 : C * ((Real.exp (τ * a) * D) ^ 2 + (Real.exp (τ * b) * S) ^ 2) ≤
      (Real.sqrt C * (Real.exp (τ * a) * D + Real.exp (τ * b) * S)) ^ 2 := by
    rw [mul_pow (Real.sqrt C), Real.sq_sqrt hC]
    exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hY hZ]) hC
  have hR : 0 ≤ Real.sqrt C * (Real.exp (τ * a) * D + Real.exp (τ * b) * S) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hY hZ)
  have h3 := Real.sqrt_le_sqrt (h1.trans h2)
  rwa [Real.sqrt_sq hX, Real.sqrt_sq hR] at h3

/-- Two separated weight gaps give the exact interpolation exponent and
a constant depending only on the weighted estimate and its threshold. -/
theorem interpolation_of_weighted_sq
    {pB p0 pH C τ0 A S D : ℝ} (hB : pB < p0) (hH : p0 < pH) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hAD : A ≤ D)
    (h : ∀ τ : ℝ, τ0 ≤ τ → τ ^ 3 * (Real.exp (2 * (τ * p0)) * A ^ 2) ≤
      C * (Real.exp (2 * (τ * pB)) * D ^ 2 + Real.exp (2 * (τ * pH)) * S ^ 2)) :
    A ≤ (2 * Real.sqrt C + Real.exp ((p0-pB) * max τ0 1)) *
      (S ^ ((p0-pB)/(pH-pB)) * D ^ (1 - (p0-pB)/(pH-pB))) := by
  have ha := sub_pos.mpr hB
  have hb := sub_pos.mpr hH
  have hbal := exp_balance (a := p0 - pB) (b := pH - p0)
    (C := Real.sqrt C) (τ0 := max τ0 1) ha hb (Real.sqrt_nonneg _) hA hS hAD
    (by
      intro τ hτ
      have h1 := weighted_sq_to_unsq ((le_max_right τ0 1).trans hτ)
        hC hA (hA.trans hAD) hS (h τ ((le_max_left τ0 1).trans hτ))
      have hE : 0 < Real.exp (τ * p0) := Real.exp_pos _
      have eB : Real.exp (τ * pB) = Real.exp (τ * p0) *
          Real.exp (-((p0 - pB) * τ)) := by
        rw [← Real.exp_add]; congr 1; ring
      have eH : Real.exp (τ * pH) = Real.exp (τ * p0) *
          Real.exp ((pH - p0) * τ) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [eB, eH] at h1
      have h2 : Real.exp (τ * p0) * A ≤ Real.exp (τ * p0) *
          (Real.sqrt C * (Real.exp (-((p0 - pB) * τ)) * D +
            Real.exp ((pH - p0) * τ) * S)) :=
        h1.trans_eq (by ring)
      exact le_of_mul_le_mul_left h2 hE)
  have hsum : p0 - pB + (pH - p0) = pH - pB := by ring
  rw [hsum] at hbal
  have hne : pH - pB ≠ 0 := by
    have hh := add_pos ha hb
    rw [hsum] at hh
    exact hh.ne'
  have hg : (pH - p0) / (pH - pB) = 1 - (p0 - pB) / (pH - pB) := by
    rw [eq_sub_iff_add_eq, ← add_div,
      show pH - p0 + (p0 - pB) = pH - pB by ring, div_self hne]
  rw [hg] at hbal
  exact hbal

/-- UI1: strict-height interpolation with the EXPLICIT constant `2√C + exp(a·max τ0 1)`. -/
theorem strictHeight_interpolation_of_weighted_sq_explicit
    {κ l e C τ0 A S D : ℝ} (hκ : 0 < κ)
    (hl : 0 < l) (hκl : κ * l ≤ 1 / 4) (he : 0 ≤ e)
    (he4 : 4 * e < κ * l ^ 2) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hAD : A ≤ D)
    (h : ∀ τ : ℝ, τ0 ≤ τ → τ ^ 3 *
      (Real.exp (2 * (τ * strictHeight κ (-e))) * A ^ 2) ≤
      C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * e))) * D ^ 2 +
        Real.exp (2 * (τ * strictHeight κ (l + 3 * e))) * S ^ 2)) :
    A ≤ (2 * Real.sqrt C + Real.exp
      ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) * max τ0 1)) *
      (S ^ ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e))) *
        D ^ (1 - (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)))) := by
  obtain ⟨ha,hb,_,_⟩ := strictExponent_bounds hκ hl hκl he he4
  exact interpolation_of_weighted_sq (sub_pos.mp ha) (sub_pos.mp hb) hC hA hS hAD h

/-- UI2: the interpolation constant exists BEFORE the norms `A, S, D`. -/
theorem strictHeight_interpolation_of_weighted_sq_uniform
    {κ l e C τ0 : ℝ} (hκ : 0 < κ) (hl : 0 < l) (hκl : κ * l ≤ 1 / 4)
    (he : 0 ≤ e) (he4 : 4 * e < κ * l ^ 2) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ A S D : ℝ, 0 ≤ A → 0 ≤ S → A ≤ D →
      (∀ τ : ℝ, τ0 ≤ τ → τ ^ 3 *
        (Real.exp (2 * (τ * strictHeight κ (-e))) * A ^ 2) ≤
        C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * e))) * D ^ 2 +
          Real.exp (2 * (τ * strictHeight κ (l + 3 * e))) * S ^ 2)) →
      A ≤ K * (S ^ ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e))) *
        D ^ (1 - (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)))) := by
  refine ⟨2 * Real.sqrt C + Real.exp
      ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) * max τ0 1),
    by positivity, fun A S D hA hS hAD h => ?_⟩
  exact strictHeight_interpolation_of_weighted_sq_explicit hκ hl hκl he he4 hC hA hS hAD h


end CalderonN.Elliptic
