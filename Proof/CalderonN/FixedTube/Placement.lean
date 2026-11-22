module

public import Proof.CalderonN.FixedTube.Strict

import Mathlib.Tactic

/-!
Adapted from `Calderon/MixedKernelConstruction/MixedKernelClosedTubeConstruction.lean`
in `anisotropic-calderon-lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc.
-/

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology InnerProductSpace

set_option maxHeartbeats 800000

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] {normal : I dim}

/-- the actual tube vector `b = a(1+σ)t^σ g_Y` satisfies `amin ≤ ‖b‖` (T6, since `g_Y 2 = 1`). -/
theorem tube_b_norm_lower_actual {M e0 a σ amin : ℝ} {Y : (X dim)} (hσ : 0 ≤ σ)
    (ht : 1 ≤ tubeHeight normal M e0 Y) (ham : 0 ≤ amin) (ha : amin ≤ a) :
    amin ≤ ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ := by
  have hg2 : tubeHeightGrad normal e0 Y normal = 1 := tubeHeightGrad_normal e0 Y
  have h := tube_b_norm_lower (g := tubeHeightGrad normal e0 Y) hg2 hσ ht ham ha
  have hc : (1 + σ) * a * tubeHeight normal M e0 Y ^ σ = a * (1 + σ) * tubeHeight normal M e0 Y ^ σ := by ring
  rwa [hc] at h

/-- outside the literal coarse seed, with `σ ≤ 1` and `‖g_Y‖ ≤ 2`, the actual `b` has `‖b‖ ≤ 4/c0`. -/
theorem tube_b_norm_upper_unseeded {M e0 a σ c0 : ℝ} {Y ω : (X dim)} (hM : 0 ≤ M) (he0 : 0 ≤ e0)
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hc0 : 0 < c0) (ht : 0 < tubeHeight normal M e0 Y)
    (hω : ‖ω‖ = 1) (hg : ‖tubeHeightGrad normal e0 Y‖ ≤ 2)
    (hout : ¬ (min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) <
      c0 * ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖)) :
    ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ ≤ 4 / c0 := by
  have hts : 0 ≤ tubeHeight normal M e0 Y ^ σ := Real.rpow_nonneg ht.le σ
  have hr : tubeRadius normal M e0 a σ Y = a * tubeHeight normal M e0 Y ^ σ * tubeHeight normal M e0 Y := by
    rw [tubeRadius, Real.rpow_add ht, Real.rpow_one]
    ring
  have hA0 : 0 ≤ a * tubeHeight normal M e0 Y ^ σ := mul_nonneg ha hts
  have hr0 : 0 ≤ tubeRadius normal M e0 a σ Y := by
    rw [hr]
    exact mul_nonneg hA0 ht.le
  have hn : ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖ = tubeRadius normal M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  rw [hn, not_lt] at hout
  have hY : c0 * tubeRadius normal M e0 a σ Y ≤ Y normal := hout.trans (min_le_right _ _)
  have htY : Y normal ≤ tubeHeight normal M e0 Y := by
    have h := mul_nonneg he0 (transversePair_nonneg normal Y)
    simp only [tubeHeight]
    linarith
  rw [hr] at hY
  have hcA : c0 * (a * tubeHeight normal M e0 Y ^ σ) ≤ 1 := by
    have h : c0 * (a * tubeHeight normal M e0 Y ^ σ) * tubeHeight normal M e0 Y ≤ 1 * tubeHeight normal M e0 Y := by
      linarith
    exact le_of_mul_le_mul_right h ht
  have hAc : a * tubeHeight normal M e0 Y ^ σ ≤ 1 / c0 := by
    rw [le_div_iff₀ hc0]
    linarith
  have hk0 : 0 ≤ a * (1 + σ) * tubeHeight normal M e0 Y ^ σ := by
    have h1σ : 0 ≤ 1 + σ := by linarith
    positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
  have hk : a * (1 + σ) * tubeHeight normal M e0 Y ^ σ ≤ 2 * (1 / c0) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - σ) hA0]
  calc a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * ‖tubeHeightGrad normal e0 Y‖ ≤ 2 * (1 / c0) * 2 :=
        mul_le_mul hk hg (norm_nonneg _) (by positivity)
    _ = 4 / c0 := by ring

private theorem tube_grad_norm_sq (e0 : ℝ) (Y : X dim) :
    ‖tubeHeightGrad normal e0 Y‖^2 = 1 + 4 * e0^2 * transversePair normal Y Y := by
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ normal)]
  simp only [tubeHeightGrad, PiLp.toLp_apply, if_true, one_pow, transversePair, Finset.mul_sum]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by
    rw [if_neg (Finset.ne_of_mem_erase hi)]
    ring

private theorem tube_grad_sub_axis_norm_sq (e0 : ℝ) (Y : X dim) :
    ‖tubeHeightGrad normal e0 Y - axis normal‖^2 = 4 * e0^2 * transversePair normal Y Y := by
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ normal)]
  simp only [tubeHeightGrad, axis, PiLp.toLp_apply, PiLp.sub_apply, EuclideanSpace.single_apply,
    if_true, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero, transversePair, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => by
    simp only [if_neg (Finset.ne_of_mem_erase hi), sub_zero]
    ring

theorem tube_grad_norm_le_two {e0 T0 : ℝ} {Y : X dim} (he0 : 0 ≤ e0)
    (hY : e0 * transversePair normal Y Y ≤ T0) (hT : e0 * T0 ≤ 3/4) :
    ‖tubeHeightGrad normal e0 Y‖ ≤ 2 := by
  have h := mul_le_mul_of_nonneg_left hY he0
  have hsq := tube_grad_norm_sq (normal := normal) e0 Y
  nlinarith [norm_nonneg (tubeHeightGrad normal e0 Y)]

theorem tube_grad_near_normal {e0 T0 η : ℝ} {Y : X dim} (he0 : 0 ≤ e0) (hη : 0 ≤ η)
    (hY : e0 * transversePair normal Y Y ≤ T0) (hT : 4 * (e0 * T0) ≤ η^2) :
    ‖tubeHeightGrad normal e0 Y - axis normal‖ ≤ η := by
  have h := mul_le_mul_of_nonneg_left hY he0
  apply (sq_le_sq₀ (norm_nonneg _) hη).mp
  rw [tube_grad_sub_axis_norm_sq]
  nlinarith

/-- outside the literal coarse seed, the actual `b = a(1+σ)t^σ g_Y = ((1+σ)(r/t)) g_Y` stays `ε`-separated
from `-ω` and `-2ω` (contraposition of T19/T20 through T10). -/
theorem tube_sep_of_unseeded {M e0 a σ c0 η ε : ℝ} {Y ω : (X dim)} (hM : 0 < M) (he0 : 0 ≤ e0)
    (ht : 0 < tubeHeight normal M e0 Y) (hr : 0 < tubeRadius normal M e0 a σ Y) (hω : ‖ω‖ = 1)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ η) (hε : ε ≤ η) (hη : 0 < η) (hη10 : η ≤ 1 / 10)
    (hc0 : 13 * η ≤ c0)
    (hge : ‖tubeHeightGrad normal e0 Y - EuclideanSpace.single normal (1 : ℝ)‖ ≤ η)
    (hout : ¬ (min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) <
      c0 * ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖)) :
    ε < ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ ∧
      ε < ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y + (2 : ℝ) • ω‖ := by
  have ht0 : tubeHeight normal M e0 Y ≠ 0 := ht.ne'
  have hk : a * (1 + σ) * tubeHeight normal M e0 Y ^ σ =
      (1 + σ) * (tubeRadius normal M e0 a σ Y / tubeHeight normal M e0 Y) := by
    rw [tubeRadius, Real.rpow_add ht, Real.rpow_one,
      mul_comm (tubeHeight normal M e0 Y) (tubeHeight normal M e0 Y ^ σ), ← mul_assoc, mul_div_cancel_right₀ _ ht0]
    ring
  have hy : Y normal < tubeHeight normal M e0 Y := by
    have h := mul_nonneg he0 (transversePair_nonneg normal Y)
    simp only [tubeHeight]
    linarith
  have hg2 : tubeHeightGrad normal e0 Y normal = 1 := tubeHeightGrad_normal e0 Y
  have hn : ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖ = tubeRadius normal M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.le]
  have hseed : Y normal + tubeRadius normal M e0 a σ Y * ω normal < c0 * tubeRadius normal M e0 a σ Y → False :=
    fun h => by
      apply hout
      rw [tube_min_height hr.le, hn]
      have hm := mul_le_mul_of_nonneg_left (min_le_left (ω normal) 0) hr.le
      linarith
  constructor
  · by_contra h
    rw [not_lt, add_comm ω, hk] at h
    exact hseed (tube_excluded_one_low hω hg2 hge hr ht hσ0 hσ hε hη (by linarith) hc0 hy h)
  · by_contra h
    rw [not_lt, hk] at h
    exact hseed (tube_excluded_two_low hω hg2 hge hr ht hσ0 hσ hε hη hη10 (by linarith) hy h)

/-- on the capped sweep `1 ≤ t ≤ U`, `0 ≤ a ≤ 2/c0 + 1`, `0 ≤ σ ≤ 1`, the actual radius is `≤ (2/c0+1) U²`. -/
theorem tube_radius_le_sweep {M e0 a σ c0 U : ℝ} {Y : (X dim)} (hc0 : 0 < c0) (ht1 : 1 ≤ tubeHeight normal M e0 Y)
    (htU : tubeHeight normal M e0 Y ≤ U) (ha0 : 0 ≤ a) (ha : a ≤ 2 / c0 + 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    tubeRadius normal M e0 a σ Y ≤ (2 / c0 + 1) * U ^ 2 := by
  have h1 : tubeHeight normal M e0 Y ^ (1 + σ) ≤ tubeHeight normal M e0 Y ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have h2 : tubeHeight normal M e0 Y ^ (2 : ℝ) ≤ U ^ 2 := by
    rw [Real.rpow_two]
    nlinarith
  have hc : 0 ≤ 2 / c0 + 1 := by
    have := div_pos (two_pos : (0 : ℝ) < 2) hc0
    linarith
  rw [tubeRadius]
  exact mul_le_mul ha (h1.trans h2) (Real.rpow_nonneg (by linarith) _) hc

/-- N10 with the N8/N9 choices exposed: `m0, σ0` are chosen without `R`; only `e00` depends on `R`. -/
theorem tube_native_strict_placement_uniform {amin Bb ε : ℝ} (ham : 0 < amin) (hε : 0 < ε)
    (hB : 0 ≤ Bb) :
    ∃ m0 σ0 : ℝ, 0 < m0 ∧ 0 < σ0 ∧ ∀ R : ℝ, 0 ≤ R → ∃ e00 : ℝ, 0 < e00 ∧ ∀ (M e0 a σ : ℝ) (Y ω : (X dim)),
      0 ≤ σ → σ ≤ σ0 → 0 ≤ e0 → e0 ≤ e00 → 0 < tubeHeight normal M e0 Y →
      0 < tubeRadius normal M e0 a σ Y → tubeRadius normal M e0 a σ Y ≤ R → ‖ω‖ = 1 →
      amin ≤ ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ →
      ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ ≤ Bb →
      ε ≤ ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ →
      ε ≤ ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y + (2 : ℝ) • ω‖ →
      ProductStrictHessianAt (fun _ => (1 : (Mat dim))) (fun _ => (1 : (Mat dim)))
          (tubePhase normal M e0 a σ) (Y + tubeRadius normal M e0 a σ Y • ω,Y) := by
  obtain ⟨m0, hm0, hN8⟩ := tube_native_strict_of_margin (normal := normal) (Bb := Bb) ham hε
  refine ⟨m0, m0 / (8 * (Bb ^ 2 * ε⁻¹ ^ 2 + 1)), hm0, by positivity, fun R hR =>
    ⟨m0 / (16 * (Bb * R * ε⁻¹ ^ 2 + 1)), by positivity, ?_⟩⟩
  intro M e0 a σ Y ω hσ hσ0 he0 he00 ht hr hrR hω hb1 hb2 hn1 hn2
  refine hN8 M e0 a σ Y ω ht hr hω hb1 hb2 hn1 hn2 (fun w hw hw1 => ?_)
  have hg2 : tubeHeightGrad normal e0 Y normal = 1 := tubeHeightGrad_normal e0 Y
  have hg1 : 1 ≤ ‖tubeHeightGrad normal e0 Y‖ := by
    have h := abs_coord_le_norm (tubeHeightGrad normal e0 Y) normal
    rw [hg2, abs_one] at h
    exact h
  have htp : 0 < tubeHeight normal M e0 Y ^ (1 + σ) := Real.rpow_pos_of_pos ht _
  have ha : 0 < a := by
    by_contra h
    have h' : a * tubeHeight normal M e0 Y ^ (1 + σ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) htp.le
    exact (not_lt.mpr h') hr
  have hk0 : 0 ≤ a * (1 + σ) * tubeHeight normal M e0 Y ^ σ := by
    have := Real.rpow_nonneg ht.le σ
    have h1σ : 0 ≤ 1 + σ := by linarith
    positivity
  have hkn : ‖(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ =
      a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * ‖tubeHeightGrad normal e0 Y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
  have hkB : a * (1 + σ) * tubeHeight normal M e0 Y ^ σ ≤ Bb := by
    rw [hkn] at hb2
    nlinarith
  have hrs : tubeRadius normal M e0 a σ Y * (a * (1 + σ) * σ * tubeHeight normal M e0 Y ^ (σ - 1)) =
      σ / (1 + σ) * (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) ^ 2 :=
    (tube_radius_hessian_coeffs (a := a) ht hσ).1
  have hd : ∀ U : (X dim), a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * tubeHeightDeriv normal e0 Y U =
      ⟪(a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y, U⟫_ℝ := fun U => by
    rw [tubeHeightDeriv_eq_inner, real_inner_smul_left]
  have hL : ∀ u : (X dim),
      ‖u‖ * ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ = 1 →
      ‖u‖ ≤ ε⁻¹ := fun u hu => by
    rw [← one_div, le_div_iff₀ hε]
    calc ‖u‖ * ε ≤ ‖u‖ * ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ :=
          mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)
      _ = 1 := hu
  have hq0 : 0 < ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ :=
    lt_of_lt_of_le hε hn1
  have hu1 : ‖(‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ ^ 2)⁻¹ •
      (ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y)‖ *
      ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    first | (field_simp; done) | (field_simp; ring)
  have hterm : ∀ u : (X dim),
      ‖u‖ * ‖ω + (a * (1 + σ) * tubeHeight normal M e0 Y ^ σ) • tubeHeightGrad normal e0 Y‖ = 1 →
      tubeRadius normal M e0 a σ Y *
        (a * (1 + σ) * σ * tubeHeight normal M e0 Y ^ (σ - 1) * tubeHeightDeriv normal e0 Y u ^ 2 +
          a * (1 + σ) * tubeHeight normal M e0 Y ^ σ * (2 * e0 * (transversePair normal u u))) ≤
        σ * Bb ^ 2 * ε⁻¹ ^ 2 + 4 * e0 * Bb * R * ε⁻¹ ^ 2 := fun u hu =>
    tube_corr_term_le hrs hσ he0 hk0 hkB hr.le hrR (by rw [hd]; exact abs_real_inner_le_norm _ _)
      (norm_nonneg _) hb2 (norm_nonneg _) (hL u hu) (transversePair_nonneg normal u) (tube_horizontal_sq_le normal u)
  have h1 := hterm _ hu1
  have h2 := hterm w hw1
  have hσm : σ * (8 * (Bb ^ 2 * ε⁻¹ ^ 2 + 1)) ≤ m0 := (le_div_iff₀ (by positivity)).mp hσ0
  have hem : e0 * (16 * (Bb * R * ε⁻¹ ^ 2 + 1)) ≤ m0 := (le_div_iff₀ (by positivity)).mp he00
  nlinarith

/-- uniform sweep order `c0, η, amin → σ → T0 → U → e0`; the height cap `U` (hence `R`) may be chosen
after `T0`. The level floor `amin` is a free positive datum here, not linked to target separations. -/
theorem tube_native_strict_sweep_uniform {c0 η amin : ℝ} (Tmin : ℝ) (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (ham : 0 < amin) :
    ∃ σ T0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ 0 < T0 ∧ Tmin < T0 ∧ 1 < c0 * amin * T0 ^ σ ∧
      ∀ U : ℝ, 1 ≤ U → ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) ∧
        ∀ (M a : ℝ) (Y ω : (X dim)), 0 < M → ‖ω‖ = 1 → 1 ≤ tubeHeight normal M e0 Y →
          tubeHeight normal M e0 Y ≤ U → e0 * (transversePair normal Y Y) ≤ T0 →
          amin ≤ a → a ≤ 2 / c0 + 1 →
          ¬ (min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) <
            c0 * ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖) →
          ProductStrictHessianAt (fun _ => (1 : (Mat dim))) (fun _ => (1 : (Mat dim)))
          (tubePhase normal M e0 a σ) (Y + tubeRadius normal M e0 a σ Y • ω,Y) := by
  have hB : 0 ≤ 4 / c0 := div_nonneg (by norm_num) hc0.le
  have hc2 : 0 ≤ 2 / c0 + 1 := by
    have := div_pos (two_pos : (0 : ℝ) < 2) hc0
    linarith
  obtain ⟨m0, σ0, _hm0, hσ0, hP⟩ := tube_native_strict_placement_uniform (normal := normal) (Bb := 4 / c0) ham hη hB
  obtain ⟨σ, hσpos, hσσ0, hση, hσ1⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ≤ σ0 ∧ σ ≤ η ∧ σ ≤ 1 := by
    have hm : 0 < min (min σ0 η) 1 := lt_min (lt_min hσ0 hη) one_pos
    have h1 : min (min σ0 η) 1 ≤ σ0 := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min σ0 η) 1 ≤ η := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : min (min σ0 η) 1 ≤ 1 := min_le_right _ _
    exact ⟨min (min σ0 η) 1 / 2, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T0, hT0pos, hTmin, hT0⟩ : ∃ T0 : ℝ, 0 < T0 ∧ Tmin < T0 ∧ 1 < c0 * amin * T0 ^ σ := by
    have hca : 0 < c0 * amin := mul_pos hc0 ham
    have hBp : 0 < 1 / (c0 * amin) := one_div_pos.mpr hca
    have hp : 0 ≤ (1 / (c0 * amin)) ^ (1 / σ) := Real.rpow_nonneg hBp.le _
    let t := (1 / (c0 * amin)) ^ (1 / σ)
    let T := max Tmin t + 1
    have ht : t < T := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
    have hmin : Tmin < T := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
    refine ⟨T, lt_of_le_of_lt hp ht, hmin, ?_⟩
    have hlt := Real.rpow_lt_rpow hp ht hσpos
    rw [← Real.rpow_mul hBp.le, one_div_mul_cancel hσpos.ne', Real.rpow_one] at hlt
    have h1 : c0 * amin * (1 / (c0 * amin)) = 1 := mul_one_div_cancel hca.ne'
    have h2 := mul_lt_mul_of_pos_left hlt hca
    linarith
  refine ⟨σ, T0, hσpos, hση, hσ1, hT0pos, hTmin, hT0, fun U hU => ?_⟩
  have hR : 0 ≤ (2 / c0 + 1) * U ^ 2 := mul_nonneg hc2 (sq_nonneg U)
  obtain ⟨e00, he00, hQ⟩ := hP ((2 / c0 + 1) * U ^ 2) hR
  obtain ⟨e0, he0pos, he0e00, he0T, he0η, he0B⟩ : ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ e00 ∧ e0 * T0 ≤ 3 / 4 ∧
      4 * (e0 * T0) ≤ η ^ 2 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) := by
    have hq1 : 0 < 3 / (4 * T0) := div_pos (by norm_num) (by linarith)
    have hq2 : 0 < η ^ 2 / (4 * T0) := div_pos (by positivity) (by linarith)
    have hq3 : 0 < 1 / ((4 / c0) ^ 2 + 1) := by positivity
    have hm0 : 0 < min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) :=
      lt_min (lt_min he00 hq1) (lt_min hq2 hq3)
    have h1 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤ e00 :=
      (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        3 / (4 * T0) := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        η ^ 2 / (4 * T0) := (min_le_right _ _).trans (min_le_left _ _)
    have h4 : min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) ≤
        1 / ((4 / c0) ^ 2 + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have h2' := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * T0)).mp h2
    have h3' := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * T0)).mp h3
    refine ⟨min (min e00 (3 / (4 * T0))) (min (η ^ 2 / (4 * T0)) (1 / ((4 / c0) ^ 2 + 1))) / 2,
      by linarith, by linarith, ?_, ?_, by linarith⟩
    · nlinarith
    · nlinarith
  refine ⟨e0, he0pos, he0B, ?_⟩
  intro M a Y ω hM hω ht1 htU hYT ha1 ha2 hout
  have ht : 0 < tubeHeight normal M e0 Y := by linarith
  have ha0 : 0 < a := ham.trans_le ha1
  have hr : 0 < tubeRadius normal M e0 a σ Y := by
    rw [tubeRadius]
    exact mul_pos ha0 (Real.rpow_pos_of_pos ht _)
  have hge := tube_grad_near_normal he0pos.le hη.le hYT he0η
  have hg2 := tube_grad_norm_le_two he0pos.le hYT he0T
  have hsep := tube_sep_of_unseeded hM he0pos.le ht hr hω hσpos.le hση le_rfl hη hη10 hc0η hge hout
  have hlow := tube_b_norm_lower_actual (M := M) (e0 := e0) (Y := Y) hσpos.le ht1 ham.le ha1
  have hup := tube_b_norm_upper_unseeded hM.le he0pos.le ha0.le hσpos.le hσ1 hc0 ht hω hg2 hout
  have hrR := tube_radius_le_sweep hc0 ht1 htU ha0.le ha2 hσpos.le hσ1
  exact hQ M e0 a σ Y ω hσpos.le hσσ0 he0pos.le he0e00 ht hr hrR hω hlow hup hsep.1.le hsep.2.le

/-- source order. The TARGET height cap `Ut` fixes `amin` (T21) before `σ`; the SWEEP height cap is `T0`
itself, chosen after `σ`; `e0` is chosen last. -/
theorem tube_native_strict_sweep_targets {c0 η d Ut : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hUt : 1 ≤ Ut) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ Ut < T0 ∧ 1 < c0 * min 1 (d / (2 * Ut ^ 2)) * T0 ^ σ ∧
      0 < e0 ∧ e0 ≤ 1 / ((4 / c0) ^ 2 + 1) ∧
      (∀ D t : ℝ, d ≤ D → 1 ≤ t → t ≤ Ut → min 1 (d / (2 * Ut ^ 2)) < D / t ^ (1 + σ)) ∧
      ∀ (M a : ℝ) (Y ω : (X dim)), 0 < M → ‖ω‖ = 1 → 1 ≤ tubeHeight normal M e0 Y →
        tubeHeight normal M e0 Y ≤ T0 → e0 * (transversePair normal Y Y) ≤ T0 →
        min 1 (d / (2 * Ut ^ 2)) ≤ a → a ≤ 2 / c0 + 1 →
        ¬ (min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) <
          c0 * ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖) →
        ProductStrictHessianAt (fun _ => (1 : (Mat dim))) (fun _ => (1 : (Mat dim)))
          (tubePhase normal M e0 a σ) (Y + tubeRadius normal M e0 a σ Y • ω,Y) := by
  have hU2 : 0 < 2 * Ut ^ 2 := by positivity
  have ham : 0 < min 1 (d / (2 * Ut ^ 2)) := lt_min one_pos (div_pos hd hU2)
  obtain ⟨σ, T0, hσpos, hση, hσ1, _hT0pos, hUtT, hT0, hU⟩ :=
    tube_native_strict_sweep_uniform (normal := normal) Ut hc0 hη hη10 hc0η ham
  obtain ⟨e0, he0pos, he0B, hS⟩ := hU (max 1 T0) (le_max_left _ _)
  refine ⟨σ, T0, e0, hσpos, hση, hσ1, hUtT, hT0, he0pos, he0B,
    fun D t hdD ht1 htU => tube_target_level_gt hd hdD ht1 htU hσpos.le hσ1, ?_⟩
  intro M a Y ω hM hω ht1 htT hYT ha1 ha2 hout
  exact hS M a Y ω hM hω ht1 (htT.trans (le_max_right _ _)) hYT ha1 ha2 hout

/-- on the source base `y_n ≥ -B-1`, `M > B+3`, `t ≤ T0`, one has `1 ≤ t` and `e0 |y'|² ≤ T0`. -/
theorem tube_base_height {M e0 B T0 : ℝ} {Y : (X dim)} (he0 : 0 ≤ e0) (hM : B + 3 < M)
    (hy : -B - 1 ≤ Y normal) (htT : tubeHeight normal M e0 Y ≤ T0) :
    1 ≤ tubeHeight normal M e0 Y ∧ e0 * (transversePair normal Y Y) ≤ T0 := by
  have h := mul_nonneg he0 (transversePair_nonneg normal Y)
  simp only [tubeHeight] at htT ⊢
  constructor <;> linarith

/-- targets with `y_n ≤ B`, `|y'|² ≤ B²` and `e0 ≤ 1` lie at height `t ≤ M + B + B²`. -/
theorem tube_target_height_le {M e0 B : ℝ} {Y : (X dim)} (he0 : 0 ≤ e0) (he01 : e0 ≤ 1)
    (hy : Y normal ≤ B) (hh : transversePair normal Y Y ≤ B ^ 2) :
    tubeHeight normal M e0 Y ≤ M + B + B ^ 2 := by
  have hh0 : 0 ≤ transversePair normal Y Y := transversePair_nonneg normal Y
  have h := mul_le_mul he01 hh hh0 zero_le_one
  simp only [tubeHeight]
  linarith

/-- N20 in the source base coordinates `y_n ≥ -B-1`, `M > B+3`, with target cap `Ut = M + B + B²`. -/
theorem tube_native_strict_sweep_base {c0 η d B M : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B) (hM : B + 3 < M) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ η ∧ σ ≤ 1 ∧ M + B + B ^ 2 < T0 ∧
      1 < c0 * min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) * T0 ^ σ ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      (∀ (D : ℝ) (Y : (X dim)), d ≤ D → -B - 1 ≤ Y normal → Y normal ≤ B → transversePair normal Y Y ≤ B ^ 2 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) < D / tubeHeight normal M e0 Y ^ (1 + σ)) ∧
      ∀ (a : ℝ) (Y ω : (X dim)), ‖ω‖ = 1 → -B - 1 ≤ Y normal → tubeHeight normal M e0 Y ≤ T0 →
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ a → a ≤ 2 / c0 + 1 →
        ¬ (min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) <
          c0 * ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖) →
        ProductStrictHessianAt (fun _ => (1 : (Mat dim))) (fun _ => (1 : (Mat dim)))
          (tubePhase normal M e0 a σ) (Y + tubeRadius normal M e0 a σ Y • ω,Y) := by
  have hUt : 1 ≤ M + B + B ^ 2 := by
    have := sq_nonneg B
    linarith
  obtain ⟨σ, T0, e0, hσpos, hση, hσ1, hUtT, hT0, he0pos, he0B, htgt, hS⟩ :=
    tube_native_strict_sweep_targets (normal := normal) hc0 hη hη10 hc0η hd hUt
  have h1 : 1 / ((4 / c0) ^ 2 + 1) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [sq_nonneg (4 / c0)]
  refine ⟨σ, T0, e0, hσpos, hση, hσ1, hUtT, hT0, he0pos, he0B.trans h1, ?_, ?_⟩
  · intro D Y hdD hy1 hy2 hh
    exact htgt D _ hdD (tube_base_height (T0 := tubeHeight normal M e0 Y) he0pos.le hM hy1 le_rfl).1
      (tube_target_height_le he0pos.le (he0B.trans h1) hy2 hh)
  · intro a Y ω hω hy htT ha1 ha2 hout
    obtain ⟨ht1, hYT⟩ := tube_base_height he0pos.le hM hy htT
    have hM0 : 0 < M := by linarith
    exact hS M a Y ω hM0 hω ht1 htT hYT ha1 ha2 hout

/-- the whole `a ≥ 2/c0 + 1` level lies in the literal coarse seed (T8). -/
theorem tube_amax_level_in_seed {M e0 a σ c0 : ℝ} {Y ω : (X dim)} (hc0 : 0 < c0) (hM : 0 ≤ M)
    (he0 : 0 ≤ e0) (ht1 : 1 ≤ tubeHeight normal M e0 Y) (hσ : 0 ≤ σ) (ha : 2 / c0 + 1 ≤ a) (hω : ‖ω‖ = 1) :
    min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) < c0 * ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖ := by
  have ha0 : 0 ≤ a := by
    have := div_pos (two_pos : (0 : ℝ) < 2) hc0
    linarith
  have hr0 : 0 ≤ tubeRadius normal M e0 a σ Y := by
    rw [tubeRadius]
    exact mul_nonneg ha0 (Real.rpow_nonneg (by linarith) _)
  have hn : ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖ = tubeRadius normal M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  have h2 : tubeHeight normal M e0 Y < c0 * tubeRadius normal M e0 a σ Y := tube_amax_level_seeded hc0 ht1 hσ ha
  have hy : Y normal ≤ tubeHeight normal M e0 Y := by
    have h := mul_nonneg he0 (transversePair_nonneg normal Y)
    simp only [tubeHeight]
    linarith
  have h1 : min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) ≤ Y normal := min_le_right _ _
  rw [hn]
  linarith

/-- the bottom base face `y_n < 0` lies in the literal coarse seed for every positive radius. -/
theorem tube_bottom_face_in_seed {M e0 a σ c0 : ℝ} {Y ω : (X dim)} (hc0 : 0 < c0)
    (hr : 0 < tubeRadius normal M e0 a σ Y) (hy : Y normal < 0) (hω : ‖ω‖ = 1) :
    min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) < c0 * ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖ := by
  have hn : ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖ = tubeRadius normal M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.le]
  have h1 : min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) ≤ Y normal := min_le_right _ _
  have h2 := mul_pos hc0 hr
  rw [hn]
  linarith

/-- where `1 < c0 amin t^σ` (the top face `t = T0`, by T9), every level `a ≥ amin` lies in the literal
coarse seed. -/
theorem tube_top_face_in_seed {M e0 a σ c0 amin : ℝ} {Y ω : (X dim)} (hc0 : 0 < c0) (hM : 0 ≤ M)
    (he0 : 0 ≤ e0) (ht : 0 < tubeHeight normal M e0 Y) (hamin : 0 ≤ amin) (ham : amin ≤ a)
    (htop : 1 < c0 * amin * tubeHeight normal M e0 Y ^ σ) (hω : ‖ω‖ = 1) :
    min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) < c0 * ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖ := by
  have hts : 0 ≤ tubeHeight normal M e0 Y ^ σ := Real.rpow_nonneg ht.le σ
  have hr : tubeRadius normal M e0 a σ Y = a * tubeHeight normal M e0 Y ^ σ * tubeHeight normal M e0 Y := by
    rw [tubeRadius, Real.rpow_add ht, Real.rpow_one]
    ring
  have ha0 : 0 ≤ a := hamin.trans ham
  have hr0 : 0 ≤ tubeRadius normal M e0 a σ Y := by
    rw [hr]
    exact mul_nonneg (mul_nonneg ha0 hts) ht.le
  have hn : ‖(Y + tubeRadius normal M e0 a σ Y • ω) - Y‖ = tubeRadius normal M e0 a σ Y := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hge : c0 * amin * tubeHeight normal M e0 Y ^ σ ≤ c0 * a * tubeHeight normal M e0 Y ^ σ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ham hc0.le) hts
  have hlt := mul_lt_mul_of_pos_right (htop.trans_le hge) ht
  have hy : Y normal ≤ tubeHeight normal M e0 Y := by
    have h := mul_nonneg he0 (transversePair_nonneg normal Y)
    simp only [tubeHeight]
    linarith
  have h1 : min ((Y + tubeRadius normal M e0 a σ Y • ω) normal) (Y normal) ≤ Y normal := min_le_right _ _
  have hc : c0 * tubeRadius normal M e0 a σ Y = c0 * a * tubeHeight normal M e0 Y ^ σ * tubeHeight normal M e0 Y := by
    rw [hr]
    ring
  rw [hn, hc]
  linarith

end CalderonN.FixedTube
