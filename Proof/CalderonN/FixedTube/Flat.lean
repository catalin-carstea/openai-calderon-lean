module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic
import Mathlib.Topology.Order.Compact

/-!
Adapted from `Calderon/MixedKernelConstruction/MixedKernelClosedTubeConstruction.lean`
in `anisotropic-calderon-lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc.
These are the fixed-separation tube calculations used in Theorem 3.1.
-/

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped InnerProductSpace Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} {normal : I dim}

theorem abs_coord_le_norm (x : (X dim)) (i : (I dim)) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le x i

/-- the source cancellation `ω·(U₁-U₂) = b·U₂` (real and imaginary parts), with
`q = (ω+b)/‖ω+b‖²`; no smallness of `b`. -/
theorem tube_flat_normal_identities {ω v b w : (X dim)} (hω : ‖ω‖ = 1) (hn : ω + b ≠ 0)
    (hv : ⟪v, ω⟫_ℝ = 0) (hw : ⟪w, ω + b⟫_ℝ = 0) :
    ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ = ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ∧
      ⟪ω, v - w⟫_ℝ = ⟪b, w⟫_ℝ := by
  have hn2 : ‖ω + b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  have hωω : ⟪ω, ω⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hω]; norm_num
  have hnn : ⟪ω + b, ω + b⟫_ℝ = ‖ω + b‖ ^ 2 := real_inner_self_eq_norm_sq _
  constructor
  · have hb : ⟪b, ω + b⟫_ℝ = ‖ω + b‖ ^ 2 - ⟪ω, ω + b⟫_ℝ := by
      have h := inner_add_left (𝕜 := ℝ) ω b (ω + b)
      rw [hnn] at h
      linarith
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hωω, hb, mul_sub,
      inv_mul_cancel₀ hn2]
  · have h1 : ⟪ω, v⟫_ℝ = ⟪v, ω⟫_ℝ := real_inner_comm v ω
    have h2 : ⟪ω, w⟫_ℝ = ⟪w, ω⟫_ℝ := real_inner_comm w ω
    have h3 : ⟪b, w⟫_ℝ = ⟪w, b⟫_ℝ := real_inner_comm w b
    have h4 := inner_add_right (𝕜 := ℝ) w ω b
    rw [inner_sub_right]
    linarith

/-- for unit `ω`, `‖u‖² - (ω·u)² = ‖π_{ω⊥} u‖²`. -/
theorem unit_norm_sq_sub_inner_sq {ω : (X dim)} (hω : ‖ω‖ = 1) (u : (X dim)) :
    ‖u‖ ^ 2 - ⟪ω, u⟫_ℝ ^ 2 = ‖u - ⟪ω, u⟫_ℝ • ω‖ ^ 2 := by
  have h1 : ⟪u, ⟪ω, u⟫_ℝ • ω⟫_ℝ = ⟪ω, u⟫_ℝ * ⟪ω, u⟫_ℝ := by
    rw [inner_smul_right, real_inner_comm]
  have h2 : ‖⟪ω, u⟫_ℝ • ω‖ = |⟪ω, u⟫_ℝ| := by
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs]
  rw [norm_sub_sq_real, h1, h2, sq_abs]
  ring

/-- the flat projected form vanishes only at `b = 0` or `b = -2ω`. -/
theorem tube_flat_zero_cases {ω v b w : (X dim)} (hω : ‖ω‖ = 1) (hn : ω + b ≠ 0)
    (hv : ⟪v, ω⟫_ℝ = 0) (hv1 : ‖v‖ = 1) (hw : ⟪w, ω + b⟫_ℝ = 0)
    (hw1 : ‖w‖ * ‖ω + b‖ = 1)
    (hP1 : (ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)) -
      ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ • ω = 0)
    (hP2 : (v - w) - ⟪ω, v - w⟫_ℝ • ω = 0) :
    b = 0 ∨ b = -(2 : ℝ) • ω := by
  have hc : ‖ω + b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)
  generalize hk1 : ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ = k1 at hP1
  have hq : (‖ω + b‖ ^ 2)⁻¹ • (ω + b) = (1 - k1) • ω := by
    rw [sub_smul, one_smul, ← sub_eq_zero.mp hP1]
    abel
  have hn' : ω + b = (‖ω + b‖ ^ 2 * (1 - k1)) • ω := by
    calc ω + b = (‖ω + b‖ ^ 2) • ((‖ω + b‖ ^ 2)⁻¹ • (ω + b)) := by
          rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      _ = _ := by rw [hq, smul_smul]
  generalize hk : ‖ω + b‖ ^ 2 * (1 - k1) = k at hn'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hn'
    exact hn hn'
  have hwω : ⟪w, ω⟫_ℝ = 0 := by
    rw [hn', inner_smul_right] at hw
    exact (mul_eq_zero.mp hw).resolve_left hk0
  have hvw : v = w := by
    have h0 : ⟪ω, v - w⟫_ℝ = 0 := by
      rw [inner_sub_right, real_inner_comm v ω, real_inner_comm w ω, hv, hwω, sub_zero]
    rw [h0, zero_smul, sub_zero] at hP2
    exact sub_eq_zero.mp hP2
  have hn1 : ‖ω + b‖ = 1 := by
    rw [← hvw, hv1, one_mul] at hw1
    exact hw1
  have hkabs : |k| = 1 := by
    have h := congrArg norm hn'
    rw [norm_smul, hω, mul_one, Real.norm_eq_abs, hn1] at h
    exact h.symm
  rcases (abs_eq zero_le_one).mp hkabs with rfl | rfl
  · left
    calc b = (ω + b) - ω := by abel
      _ = 0 := by rw [hn', one_smul, sub_self]
  · right
    calc b = (ω + b) - ω := by abel
      _ = -(2 : ℝ) • ω := by rw [hn', neg_smul, one_smul, neg_smul, two_smul]; abel

/-- the exact flat tube form is the sum of the two `ω⊥`-projected squares. -/
theorem tube_flat_form_eq {ω v b w : (X dim)} (hω : ‖ω‖ = 1) (hn : ω + b ≠ 0)
    (hv : ⟪v, ω⟫_ℝ = 0) (hw : ⟪w, ω + b⟫_ℝ = 0) :
    ‖ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)‖ ^ 2 + ‖v - w‖ ^ 2 -
        ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ^ 2 - ⟪b, w⟫_ℝ ^ 2 =
      ‖(ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)) -
          ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ • ω‖ ^ 2 +
        ‖(v - w) - ⟪ω, v - w⟫_ℝ • ω‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := tube_flat_normal_identities hω hn hv hw
  rw [← h1, ← h2, ← unit_norm_sq_sub_inner_sq hω, ← unit_norm_sq_sub_inner_sq hω]
  ring

/-- the flat tube form is strictly positive away from `b = 0` and `b = -2ω`. -/
theorem tube_flat_form_pos {ω v b w : (X dim)} (hω : ‖ω‖ = 1) (hn : ω + b ≠ 0)
    (hv : ⟪v, ω⟫_ℝ = 0) (hv1 : ‖v‖ = 1) (hw : ⟪w, ω + b⟫_ℝ = 0)
    (hw1 : ‖w‖ * ‖ω + b‖ = 1) (hb0 : b ≠ 0) (hb2 : b ≠ -(2 : ℝ) • ω) :
    0 < ‖ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)‖ ^ 2 + ‖v - w‖ ^ 2 -
        ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ^ 2 - ⟪b, w⟫_ℝ ^ 2 := by
  rw [tube_flat_form_eq hω hn hv hw]
  by_contra hle
  push_neg at hle
  have hA := sq_nonneg ‖(ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)) -
    ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ • ω‖
  have hB := sq_nonneg ‖(v - w) - ⟪ω, v - w⟫_ℝ • ω‖
  have hA0 : ‖(ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)) -
      ⟪ω, ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ • ω‖ = 0 :=
    pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linarith)
  have hB0 : ‖(v - w) - ⟪ω, v - w⟫_ℝ • ω‖ = 0 :=
    pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linarith)
  rcases tube_flat_zero_cases hω hn hv hv1 hw hw1 (norm_eq_zero.mp hA0) (norm_eq_zero.mp hB0)
    with h | h
  · exact hb0 h
  · exact hb2 h

/-- `|b| ≥ amin` on every tube level `a ≥ amin`, since the gradient has `g₂ = 1`. -/
theorem tube_b_norm_lower {g : (X dim)} {σ t a amin : ℝ} (hg : g normal = 1) (hσ : 0 ≤ σ)
    (ht : 1 ≤ t) (ham : 0 ≤ amin) (ha : amin ≤ a) :
    amin ≤ ‖((1 + σ) * a * t ^ σ) • g‖ := by
  have hg1 : 1 ≤ ‖g‖ := by
    have h := abs_coord_le_norm g normal
    rw [hg, abs_one] at h
    exact h
  have htσ : 1 ≤ t ^ σ := Real.one_le_rpow ht hσ
  have ha0 : 0 ≤ a := ham.trans ha
  have h1 : a ≤ (1 + σ) * a := by nlinarith
  have h2 : (1 + σ) * a ≤ (1 + σ) * a * t ^ σ :=
    le_mul_of_one_le_right (by positivity) htσ
  have hk0 : 0 ≤ (1 + σ) * a * t ^ σ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk0]
  calc amin ≤ (1 + σ) * a * t ^ σ := by linarith
    _ ≤ (1 + σ) * a * t ^ σ * ‖g‖ := le_mul_of_one_le_right hk0 hg1

/-- the smallest tube radius stays below half the target separation. -/
theorem tube_amin_radius_le {d U t σ : ℝ} (hd : 0 < d) (ht1 : 1 ≤ t) (htU : t ≤ U)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    min 1 (d / (2 * U ^ 2)) * t ^ (1 + σ) ≤ d / 2 := by
  have h1 : t ^ (1 + σ) ≤ t ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  rw [Real.rpow_two] at h1
  have h2 : t ^ 2 ≤ U ^ 2 := by nlinarith
  have hU2 : 0 < U ^ 2 := by nlinarith
  have hm : min 1 (d / (2 * U ^ 2)) ≤ d / (2 * U ^ 2) := min_le_right _ _
  have hr0 : 0 ≤ t ^ (1 + σ) := Real.rpow_nonneg (by linarith) _
  calc min 1 (d / (2 * U ^ 2)) * t ^ (1 + σ) ≤ d / (2 * U ^ 2) * U ^ 2 :=
        mul_le_mul hm (h1.trans h2) hr0 (by positivity)
    _ = d / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hU2.ne']

/-- the top tube level `a ≥ 2/c0 + 1` has radius larger than `t / c0`. -/
theorem tube_amax_level_seeded {c0 t σ a : ℝ} (hc0 : 0 < c0) (ht1 : 1 ≤ t) (hσ : 0 ≤ σ)
    (ha : 2 / c0 + 1 ≤ a) : t < c0 * (a * t ^ (1 + σ)) := by
  have h1 : t ≤ t ^ (1 + σ) := by
    have h := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : (1 : ℝ) ≤ 1 + σ)
    rwa [Real.rpow_one] at h
  have h22 : c0 * (2 / c0) = 2 := by field_simp
  have h2 : 2 + c0 ≤ c0 * a := by
    have h := mul_le_mul_of_nonneg_left ha hc0.le
    rw [mul_add, h22, mul_one] at h
    exact h
  calc t < (2 + c0) * t := by nlinarith
    _ ≤ (c0 * a) * t ^ (1 + σ) := mul_le_mul h2 h1 (by linarith) (by linarith)
    _ = c0 * (a * t ^ (1 + σ)) := by ring

/-- `T0 > (1/(c0 amin))^(1/σ)` puts the top base face in the coarse seed scale. -/
theorem tube_top_face_seeded {c0 amin σ T0 : ℝ} (hc0 : 0 < c0) (ham : 0 < amin) (hσ : 0 < σ)
    (hT : (1 / (c0 * amin)) ^ (1 / σ) < T0) : 1 < c0 * amin * T0 ^ σ := by
  have hK : 0 < 1 / (c0 * amin) := by positivity
  have h1 := Real.rpow_lt_rpow (Real.rpow_nonneg hK.le _) hT hσ
  rw [← Real.rpow_mul hK.le, one_div_mul_cancel hσ.ne', Real.rpow_one] at h1
  have h2 : c0 * amin * (1 / (c0 * amin)) = 1 := by field_simp
  calc (1 : ℝ) = c0 * amin * (1 / (c0 * amin)) := h2.symm
    _ < c0 * amin * T0 ^ σ := mul_lt_mul_of_pos_left h1 (by positivity)

/-- along a tube ray the lower height is `y₂ + r min(ω₂, 0)`. -/
theorem tube_min_height {y ω : (X dim)} {r : ℝ} (hr : 0 ≤ r) :
    min ((y + r • ω) normal) (y normal) = y normal + r * min (ω normal) 0 := by
  have h : (y + r • ω) normal = y normal + r * ω normal := by simp [PiLp.add_apply, PiLp.smul_apply]
  rw [h]
  rcases le_total (ω normal) 0 with hω | hω
  · rw [min_eq_left hω, min_eq_left (by nlinarith)]
  · rw [min_eq_right hω, min_eq_right (by nlinarith), mul_zero, add_zero]

/-- the coarse seed inequality is upward closed in the tube radius. -/
theorem tube_seed_upward {y ω : (X dim)} {c0 r r' : ℝ} (hω : ‖ω‖ = 1) (hc0 : 0 < c0)
    (hr : 0 ≤ r) (hrr : r ≤ r')
    (hseed : min ((y + r • ω) normal) (y normal) < c0 * ‖(y + r • ω) - y‖) :
    min ((y + r' • ω) normal) (y normal) < c0 * ‖(y + r' • ω) - y‖ := by
  have hr' : 0 ≤ r' := hr.trans hrr
  have hn : ∀ s : ℝ, 0 ≤ s → ‖(y + s • ω) - y‖ = s := fun s hs => by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_nonneg hs]
  rw [tube_min_height hr, hn r hr] at hseed
  rw [tube_min_height hr', hn r' hr']
  have hm : min (ω normal) 0 ≤ 0 := min_le_right _ _
  nlinarith [mul_nonneg (sub_nonneg.2 hrr) (by linarith : (0 : ℝ) ≤ c0 - min (ω normal) 0)]

/-- a positive lower bound `m0` for the flat tube form on the fixed compact parameter set;
`m0` depends only on `amin, Bb, ε`. -/
theorem tube_flat_form_compact_min {amin Bb ε : ℝ} (ham : 0 < amin) (hε : 0 < ε) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ ω v b w : (X dim), ‖ω‖ = 1 → ⟪v, ω⟫_ℝ = 0 → ‖v‖ = 1 →
      ⟪w, ω + b⟫_ℝ = 0 → ‖w‖ * ‖ω + b‖ = 1 → amin ≤ ‖b‖ → ‖b‖ ≤ Bb → ε ≤ ‖ω + b‖ →
      ε ≤ ‖b + (2 : ℝ) • ω‖ →
      m0 ≤ ‖ω - (‖ω + b‖ ^ 2)⁻¹ • (ω + b)‖ ^ 2 + ‖v - w‖ ^ 2 -
        ⟪b, (‖ω + b‖ ^ 2)⁻¹ • (ω + b)⟫_ℝ ^ 2 - ⟪b, w⟫_ℝ ^ 2 := by
  let K : Set ((X dim) × (X dim) × (X dim) × (X dim)) := {p | ‖p.1‖ = 1 ∧ ⟪p.2.1, p.1⟫_ℝ = 0 ∧ ‖p.2.1‖ = 1 ∧
    ⟪p.2.2.2, p.1 + p.2.2.1⟫_ℝ = 0 ∧ ‖p.2.2.2‖ * ‖p.1 + p.2.2.1‖ = 1 ∧ amin ≤ ‖p.2.2.1‖ ∧
    ‖p.2.2.1‖ ≤ Bb ∧ ε ≤ ‖p.1 + p.2.2.1‖ ∧ ε ≤ ‖p.2.2.1 + (2 : ℝ) • p.1‖}
  obtain ⟨c, hc, hcK⟩ : ∃ c : (X dim) × (X dim) × (X dim) × (X dim) → ℝ, Continuous c ∧
      ∀ p ∈ K, c p = (‖p.1 + p.2.2.1‖ ^ 2)⁻¹ := by
    refine ⟨fun p => (max (‖p.1 + p.2.2.1‖ ^ 2) (ε ^ 2))⁻¹, ?_, ?_⟩
    · exact Continuous.inv₀ (by fun_prop)
        (fun p => (lt_max_of_lt_right (by positivity)).ne')
    · intro p hp
      have hle : ε ^ 2 ≤ ‖p.1 + p.2.2.1‖ ^ 2 := by nlinarith [hp.2.2.2.2.2.2.2.1]
      simp only [max_eq_left hle]
  let F : (X dim) × (X dim) × (X dim) × (X dim) → ℝ := fun p =>
    ‖p.1 - c p • (p.1 + p.2.2.1)‖ ^ 2 + ‖p.2.1 - p.2.2.2‖ ^ 2 -
      ⟪p.2.2.1, c p • (p.1 + p.2.2.1)⟫_ℝ ^ 2 - ⟪p.2.2.1, p.2.2.2⟫_ℝ ^ 2
  have hF : Continuous F := by fun_prop
  have hFK : ∀ p ∈ K, F p = ‖p.1 - (‖p.1 + p.2.2.1‖ ^ 2)⁻¹ • (p.1 + p.2.2.1)‖ ^ 2 +
      ‖p.2.1 - p.2.2.2‖ ^ 2 - ⟪p.2.2.1, (‖p.1 + p.2.2.1‖ ^ 2)⁻¹ • (p.1 + p.2.2.1)⟫_ℝ ^ 2 -
      ⟪p.2.2.1, p.2.2.2⟫_ℝ ^ 2 := fun p hp => by
    simp only [F, hcK p hp]
  have hKc : IsClosed K := by
    simp only [K, Set.setOf_and]
    refine (isClosed_eq ?_ ?_).inter ((isClosed_eq ?_ ?_).inter ((isClosed_eq ?_ ?_).inter
      ((isClosed_eq ?_ ?_).inter ((isClosed_eq ?_ ?_).inter ((isClosed_le ?_ ?_).inter
      ((isClosed_le ?_ ?_).inter ((isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_))))))))
    all_goals fun_prop
  have hKb : Bornology.IsBounded K := by
    refine isBounded_iff_forall_norm_le.mpr ⟨max (max 1 Bb) (1 / ε), fun p hp => ?_⟩
    obtain ⟨h1, -, h3, -, h5, -, h7, h8, -⟩ := hp
    have hw : ‖p.2.2.2‖ ≤ 1 / ε := by
      rw [le_div_iff₀ hε]
      calc ‖p.2.2.2‖ * ε ≤ ‖p.2.2.2‖ * ‖p.1 + p.2.2.1‖ :=
            mul_le_mul_of_nonneg_left h8 (norm_nonneg _)
        _ = 1 := h5
    refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩⟩
    · rw [h1]; exact (le_max_left _ _).trans (le_max_left _ _)
    · rw [h3]; exact (le_max_left _ _).trans (le_max_left _ _)
    · exact h7.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact hw.trans (le_max_right _ _)
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  have hpos : ∀ p ∈ K, 0 < F p := fun p hp => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hp
    rw [hFK p ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩]
    have hn : p.1 + p.2.2.1 ≠ 0 := fun h => by
      rw [h, norm_zero] at h8; linarith
    have hb0 : p.2.2.1 ≠ 0 := fun h => by
      rw [h, norm_zero] at h6; linarith
    have hb2 : p.2.2.1 ≠ -(2 : ℝ) • p.1 := fun h => by
      rw [h, neg_smul, neg_add_cancel, norm_zero] at h9; linarith
    exact tube_flat_form_pos h1 hn h2 h3 h4 h5 hb0 hb2
  rcases K.eq_empty_or_nonempty with hK | hK
  · refine ⟨1, one_pos, fun ω v b w h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_⟩
    have hmem : (ω, v, b, w) ∈ K := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    rw [hK] at hmem
    exact hmem.elim
  · obtain ⟨p0, hp0, hmin⟩ := hKcpt.exists_isMinOn hK hF.continuousOn
    refine ⟨F p0, hpos p0 hp0, fun ω v b w h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_⟩
    have hmem : (ω, v, b, w) ∈ K := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    have h : F p0 ≤ F (ω, v, b, w) := hmin hmem
    rw [hFK _ hmem] at h
    exact h

/-- the horizontal gradient deviation `2 e0 |y'|` is at most `2 √(e0 T0)`. -/
theorem tube_grad_dev_le {e0 s T0 : ℝ} (he0 : 0 < e0) (hs : 0 ≤ s) (hT : e0 * s ^ 2 ≤ T0) :
    2 * e0 * s ≤ 2 * Real.sqrt (e0 * T0) := by
  have h : e0 * s ≤ Real.sqrt (e0 * T0) := Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

/-- scalar coefficients of `r D²r` for `r = a t^(1+σ)`. -/
theorem tube_radius_hessian_coeffs {a σ t : ℝ} (ht : 0 < t) (hσ : 0 ≤ σ) :
    a * t ^ (1 + σ) * (a * (1 + σ) * σ * t ^ (σ - 1)) = σ / (1 + σ) * (a * (1 + σ) * t ^ σ) ^ 2 ∧
      a * t ^ (1 + σ) * (a * (1 + σ) * t ^ σ) =
        a * t ^ (1 + σ) / t * (1 + σ) * (a * t ^ (1 + σ)) := by
  have h1 : t ^ (1 + σ) = t * t ^ σ := by rw [Real.rpow_add ht, Real.rpow_one]
  have h2 : t ^ (σ - 1) = t ^ σ / t := Real.rpow_sub_one ht.ne' σ
  have htt : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hss : (1 + σ) * (1 + σ)⁻¹ = 1 := mul_inv_cancel₀ (by linarith : (0 : ℝ) < 1 + σ).ne'
  rw [h1, h2]
  constructor
  · linear_combination (a ^ 2 * (1 + σ) * σ * (t ^ σ) ^ 2) * htt -
      (a ^ 2 * σ * (1 + σ) * (t ^ σ) ^ 2) * hss
  · linear_combination (-(a ^ 2 * (1 + σ) * t * (t ^ σ) ^ 2)) * htt

/-- height bound in an excluded configuration `‖b + j ω‖ ≤ ε`, `b = (1+σ)(r/t) g`. -/
theorem tube_excluded_height {ω g : (X dim)} {j ε r t σ y2 : ℝ} (hj : 0 < j) (hg : g normal = 1)
    (hr : 0 < r) (ht : 0 < t) (hσ : 0 ≤ σ) (hy : y2 < t)
    (hb : ‖((1 + σ) * (r / t)) • g + j • ω‖ ≤ ε) :
    y2 + r * ω normal < r * ((1 + σ) / ((1 + σ) * (r / t)) + (ε - (1 + σ) * (r / t)) / j) := by
  have h1σ : (1 + σ) ≠ 0 := (by linarith : (0 : ℝ) < 1 + σ).ne'
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have hrt : r * ((1 + σ) / ((1 + σ) * (r / t))) = t := by
    rw [div_mul_eq_div_div, div_self h1σ, one_div_div]
    linear_combination t * hrr
  set κ := (1 + σ) * (r / t) with hκ
  have hcoord : |(κ • g + j • ω) normal| ≤ ε := (abs_coord_le_norm _ normal).trans hb
  have h2 : (κ • g + j • ω) normal = κ + j * ω normal := by
    simp [PiLp.add_apply, PiLp.smul_apply, hg]
  rw [h2] at hcoord
  have hω2 : ω normal ≤ (ε - κ) / j := by
    rw [le_div_iff₀ hj]
    linarith [(abs_le.mp hcoord).2]
  have h3 := mul_le_mul_of_nonneg_left hω2 hr.le
  rw [mul_add, hrt]
  linarith

/-- the `j = 1` excluded configuration lies below the seed threshold `c0`. -/
theorem tube_excluded_scalar_one {c0 η σ ε κ : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hc0 : 13 * η ≤ c0) (hσ0 : 0 ≤ σ) (hσ : σ ≤ η) (hε : ε ≤ η) (hκ : 0 < κ)
    (hκη : 1 - η ≤ κ * (1 + η)) :
    (1 + σ) / κ + (ε - κ) < c0 := by
  have h1 : 1 - 2 * η ≤ κ := by nlinarith
  have h2 : 1 - 4 * η ≤ κ ^ 2 := by nlinarith
  have h3 : 6 * η ≤ (c0 - ε) * κ := by nlinarith
  have h4 : (1 + σ) / κ < c0 - ε + κ := by
    rw [div_lt_iff₀ hκ]
    nlinarith
  linarith

/-- `‖κ g + j ω‖ ≤ ε` and `‖g - e₂‖ ≤ η` force `κ (1 + η) ≥ j - η`. -/
theorem tube_excluded_kappa_link {ω g : (X dim)} {j κ ε η : ℝ} (hω : ‖ω‖ = 1) (hj : 0 < j)
    (hκ : 0 ≤ κ) (hg : ‖g - EuclideanSpace.single normal (1 : ℝ)‖ ≤ η) (hε : ε ≤ η)
    (hb : ‖κ • g + j • ω‖ ≤ ε) : j - η ≤ κ * (1 + η) := by
  have he : ‖EuclideanSpace.single normal (1 : ℝ)‖ = 1 := by
    rw [EuclideanSpace.norm_single, norm_one]
  have hg1 : ‖g‖ ≤ 1 + η := by
    have h := norm_add_le (g - EuclideanSpace.single normal (1 : ℝ))
      (EuclideanSpace.single normal (1 : ℝ))
    rw [sub_add_cancel, he] at h
    linarith
  have hjω : ‖j • ω‖ = j := by rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hj]
  have hb' : j - ε ≤ ‖κ • g‖ := by
    have h := norm_sub_le (κ • g + j • ω) (κ • g)
    rw [add_sub_cancel_left, hjω] at h
    linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ] at hb'
  nlinarith [mul_le_mul_of_nonneg_left hg1 hκ]

/-- the `j = 2` excluded configuration lies below the seed threshold `c0`. -/
theorem tube_excluded_scalar_two {c0 η σ ε κ : ℝ} (hη : 0 < η) (hη10 : η ≤ 1 / 10)
    (hc0 : 0 < c0) (hσ : σ ≤ η) (hε : ε ≤ η) (hκ : 0 < κ)
    (hκη : 2 - η ≤ κ * (1 + η)) :
    (1 + σ) / κ + (ε - κ) / 2 < c0 := by
  have h1 : 2 - 3 * η ≤ κ := by nlinarith
  have h2 : 11 / 10 < κ * (κ - ε) / 2 := by nlinarith
  have h4 : (1 + σ) / κ < c0 + (κ - ε) / 2 := by
    rw [div_lt_iff₀ hκ]
    nlinarith
  linarith

/-- near `b = -ω` the outer point is below the coarse seed height `c0 r`. -/
theorem tube_excluded_one_low {ω g : (X dim)} {c0 η σ ε r t y2 : ℝ} (hω : ‖ω‖ = 1) (hg : g normal = 1)
    (hge : ‖g - EuclideanSpace.single normal (1 : ℝ)‖ ≤ η) (hr : 0 < r) (ht : 0 < t)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ η) (hε : ε ≤ η) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hc0 : 13 * η ≤ c0)
    (hy : y2 < t) (hb : ‖((1 + σ) * (r / t)) • g + ω‖ ≤ ε) :
    y2 + r * ω normal < c0 * r := by
  have hb1 : ‖((1 + σ) * (r / t)) • g + (1 : ℝ) • ω‖ ≤ ε := by rwa [one_smul]
  have hκ : 0 < (1 + σ) * (r / t) := by positivity
  have h1 := tube_excluded_height one_pos hg hr ht hσ0 hy hb1
  have h2 := tube_excluded_kappa_link hω one_pos hκ.le hge hε hb1
  have h3 := tube_excluded_scalar_one hη hη4 hc0 hσ0 hσ hε hκ h2
  rw [div_one] at h1
  nlinarith

/-- near `b = -2ω` the outer point is below the coarse seed height `c0 r`. -/
theorem tube_excluded_two_low {ω g : (X dim)} {c0 η σ ε r t y2 : ℝ} (hω : ‖ω‖ = 1) (hg : g normal = 1)
    (hge : ‖g - EuclideanSpace.single normal (1 : ℝ)‖ ≤ η) (hr : 0 < r) (ht : 0 < t)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ η) (hε : ε ≤ η) (hη : 0 < η) (hη10 : η ≤ 1 / 10) (hc0 : 0 < c0)
    (hy : y2 < t) (hb : ‖((1 + σ) * (r / t)) • g + (2 : ℝ) • ω‖ ≤ ε) :
    y2 + r * ω normal < c0 * r := by
  have hκ : 0 < (1 + σ) * (r / t) := by positivity
  have h1 := tube_excluded_height two_pos hg hr ht hσ0 hy hb
  have h2 := tube_excluded_kappa_link hω two_pos hκ.le hge hε hb
  have h3 := tube_excluded_scalar_two hη hη10 hc0 hσ hε hκ h2
  nlinarith

/-- every target separation `D ≥ d` sits at a tube level strictly above `amin`. -/
theorem tube_target_level_gt {d D U t σ : ℝ} (hd : 0 < d) (hdD : d ≤ D) (ht1 : 1 ≤ t)
    (htU : t ≤ U) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    min 1 (d / (2 * U ^ 2)) < D / t ^ (1 + σ) := by
  have hpos : 0 < t ^ (1 + σ) := Real.rpow_pos_of_pos (by linarith) _
  rw [lt_div_iff₀ hpos]
  have h := tube_amin_radius_le hd ht1 htU hσ0 hσ1
  linarith

end CalderonN.FixedTube
