module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators

namespace CalderonPaper

variable {P E V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The dependence of the k-th order-one symbol term on the radius of the covector. -/
@[expose] def angularSymbolScale (k : ℕ) (r : ℝ) : ℝ := r * r⁻¹ ^ k

/-- Extend a coefficient on the unit covectors along each positive ray. -/
@[expose] def homogeneousAngularCoefficient
    (b : ℕ → P → E → V) (k : ℕ) (p : P) (ξ : E) : V :=
  angularSymbolScale k ‖ξ‖ • b k p (‖ξ‖⁻¹ • ξ)

/-- The remainder for the normalized symbol at reciprocal frequency scale h. -/
@[expose] def normalizedAnnulusRemainder
    (a : P → E → V) (b : ℕ → P → E → V)
    (N : ℕ) (h : ℝ) (p : P) (η : E) : V :=
  h • a p (h⁻¹ • η) - ∑ k ∈ Finset.range N, h^k • b k p η

private theorem asymptotic_power_coefficients_unique (u v : ℕ → V)
    (h : ∀ N, ∃ C : ℝ, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖∑ k ∈ Finset.range N, t^k • (u k - v k)‖ ≤ C * t^N) :
    ∀ k, u k = v k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨C, hC⟩ := h (k + 1)
    have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖u k - v k‖ ≤ C * t := by
      filter_upwards [hC, self_mem_nhdsWithin] with t ht hpos
      have ht0 : 0 < t := hpos
      have hprev : (∑ j ∈ Finset.range k, t^j • (u j - v j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [ih j (Finset.mem_range.mp hj), sub_self, smul_zero]
      rw [Finset.sum_range_succ, hprev, zero_add, norm_smul, Real.norm_eq_abs,
        abs_of_pos (pow_pos ht0 k), pow_succ] at ht
      apply (mul_le_mul_iff_of_pos_left (pow_pos ht0 k)).mp
      simpa only [mul_assoc, mul_left_comm, mul_comm] using ht
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_id : Tendsto id (𝓝 (0 : ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds
    have ht0 : Tendsto (fun t : ℝ => C * t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hid
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht0 hbound) (norm_nonneg _)))

private theorem angularSymbolScale_mul (k : ℕ) (r s : ℝ) :
    angularSymbolScale k (r * s) = angularSymbolScale k r * angularSymbolScale k s := by
  simp only [angularSymbolScale, mul_inv_rev, mul_pow]
  ring

private theorem normalize_smul (c : ℝ) {ξ : E} (hc : 0 < c) :
    (‖c • ξ‖⁻¹ : ℝ) • (c • ξ) = ‖ξ‖⁻¹ • ξ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hc.ne', mul_one]

theorem homogeneousAngularCoefficient_smul (b : ℕ → P → E → V) (k : ℕ) (p : P)
    (c : ℝ) (ξ : E) (hc : 0 < c) :
    homogeneousAngularCoefficient b k p (c • ξ) =
      angularSymbolScale k c • homogeneousAngularCoefficient b k p ξ := by
  unfold homogeneousAngularCoefficient
  rw [normalize_smul c hc, norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      angularSymbolScale_mul, smul_smul]

private theorem normalizedAnnulusRemainder_scale
    (a : P → E → V) (b : ℕ → P → E → V) (N : ℕ)
    {h c : ℝ} (hh : h ≠ 0) (hc : c ≠ 0) (p : P) (η : E) :
    c • normalizedAnnulusRemainder a b N (h / c) p (c⁻¹ • η) =
      h • a p (h⁻¹ • η) -
        ∑ k ∈ Finset.range N, h^k • (angularSymbolScale k c • b k p (c⁻¹ • η)) := by
  unfold normalizedAnnulusRemainder
  have hscale : (h / c)⁻¹ • (c⁻¹ • η) = h⁻¹ • η := by
    rw [smul_smul, inv_div, div_eq_mul_inv]
    congr 1
    field_simp
  have hmult : c * (h / c) = h := by field_simp
  rw [hscale, smul_sub, smul_smul, hmult, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_smul]
  congr 1
  simp only [angularSymbolScale, div_eq_mul_inv, inv_pow]
  ring

/-- Comparing the same ray at two reciprocal scales forces homogeneous
coefficients, without any summation of an infinite series. -/
theorem coefficients_eq_homogeneous_of_annulus
    (a : P → E → V) (b : ℕ → P → E → V) (p : P)
    (h : ∀ η : E, (1/2 : ℝ) ≤ ‖η‖ → ‖η‖ ≤ 2 →
      ∀ N, ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
        ‖normalizedAnnulusRemainder a b N t p η‖ ≤ C * t^N)
    (η : E) (hηl : (1/2 : ℝ) ≤ ‖η‖) (hηu : ‖η‖ ≤ 2) (k : ℕ) :
    b k p η = homogeneousAngularCoefficient b k p η := by
  let c := ‖η‖
  have hc : 0 < c := by dsimp [c]; linarith
  let dir : E := c⁻¹ • η
  have hdir : ‖dir‖ = 1 := by
    dsimp only [dir]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    exact inv_mul_cancel₀ hc.ne'
  refine asymptotic_power_coefficients_unique (fun j => b j p η)
    (fun j => homogeneousAngularCoefficient b j p η) ?_ k
  intro N
  obtain ⟨C₁, hC₁⟩ := h η hηl hηu N
  obtain ⟨C₂, hC₂⟩ := h dir (by rw [hdir]; norm_num) (by rw [hdir]; norm_num) N
  refine ⟨C₁ + c * C₂ * (c⁻¹)^N, ?_⟩
  have hpos : 0 < min (1 : ℝ) c := lt_min (by norm_num) hc
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hpos)] with
    t ht₀ htmin
  have ht : 0 < t := ht₀
  have htlt : t < min (1 : ℝ) c := htmin
  have ht1 : t ≤ 1 := le_trans htlt.le (min_le_left _ _)
  have htc : t ≤ c := le_trans htlt.le (min_le_right _ _)
  have hdiv : t / c ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos ht hc, (div_le_one₀ hc).mpr htc⟩
  have hrearrange :
      (∑ j ∈ Finset.range N, t^j • (b j p η - homogeneousAngularCoefficient b j p η)) =
        c • normalizedAnnulusRemainder a b N (t / c) p dir -
          normalizedAnnulusRemainder a b N t p η := by
    rw [show dir = c⁻¹ • η by rfl, normalizedAnnulusRemainder_scale a b N ht.ne' hc.ne',
      normalizedAnnulusRemainder]
    simp only [smul_sub, Finset.sum_sub_distrib, homogeneousAngularCoefficient, c]
    abel
  rw [hrearrange]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  calc
    c * ‖normalizedAnnulusRemainder a b N (t / c) p dir‖ +
        ‖normalizedAnnulusRemainder a b N t p η‖ ≤
      c * (C₂ * (t / c)^N) + C₁ * t^N :=
        add_le_add (mul_le_mul_of_nonneg_left (hC₂ _ hdiv) hc.le) (hC₁ _ ⟨ht, ht1⟩)
    _ = (C₁ + c * C₂ * c⁻¹^N) * t^N := by
      simp only [div_eq_mul_inv, inv_pow]
      ring

end CalderonPaper
