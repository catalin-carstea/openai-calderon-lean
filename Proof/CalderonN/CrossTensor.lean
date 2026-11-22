module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The tensor series in the extension from a cross. The product L²
identities adapt the earlier `MixedKernelConstructionC3SupportV015.lean`
at revision d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

public section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace Topology

namespace LocalMetricExtension

/-- The square integral of a real L2 class is its squared norm. -/
theorem integral_sq_eq_norm_sq {α : Type*} [MeasurableSpace α] {m : Measure α}
    (u : Lp ℝ 2 m) : ∫ x, (u x) ^ 2 ∂m = ‖u‖ ^ 2 := by
  calc ∫ x, (u x) ^ 2 ∂m = ∫ x, inner ℝ (u x) (u x) ∂m := by
        apply integral_congr_ae
        exact ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs, sq_abs] using
          (real_inner_self_eq_norm_sq (u q)).symm)
    _ = inner ℝ u u := (L2.inner_def u u).symm
    _ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u

/-- The product of two real L2 classes is L2 on the product measure. -/
theorem tensor_memLp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite n] (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    MemLp (fun z : α × β => f z.1 * g z.2) 2 (m.prod n) := by
  have hf2 : Integrable (fun x => (f x) ^ 2) m := (Lp.memLp f).integrable_sq
  have hg2 : Integrable (fun y => (g y) ^ 2) n := (Lp.memLp g).integrable_sq
  have hmeas : AEStronglyMeasurable (fun z : α × β => f z.1 * g z.2) (m.prod n) :=
    ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
      ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd)
  have hsq : (fun z : α × β => (f z.1 * g z.2) ^ 2) = fun z => (f z.1) ^ 2 * (g z.2) ^ 2 := by
    funext z
    ring
  refine (memLp_two_iff_integrable_sq hmeas).mpr ?_
  rw [hsq]
  exact hf2.mul_prod hg2

/-- The tensor class `f ⊗ g ∈ L²(m × n)`. -/
def tensorLp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite n] (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    Lp ℝ 2 (m.prod n) :=
  (tensor_memLp f g).toLp _

theorem tensorLp_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite n] (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    (tensorLp f g : α × β → ℝ) =ᵐ[m.prod n] fun z => f z.1 * g z.2 :=
  (tensor_memLp f g).coeFn_toLp

/-- The exact product-norm identity `‖f ⊗ g‖ = ‖f‖ ‖g‖` (Fubini–Tonelli). -/
theorem norm_tensorLp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n] (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    ‖tensorLp f g‖ = ‖f‖ * ‖g‖ := by
  have h2 : ∫ z, ((tensorLp f g : Lp ℝ 2 (m.prod n)) z) ^ 2 ∂(m.prod n) =
      ‖f‖ ^ 2 * ‖g‖ ^ 2 := by
    calc ∫ z, ((tensorLp f g : Lp ℝ 2 (m.prod n)) z) ^ 2 ∂(m.prod n)
          = ∫ z, (f z.1) ^ 2 * (g z.2) ^ 2 ∂(m.prod n) := by
            apply integral_congr_ae
            filter_upwards [tensorLp_ae f g] with z hz
            rw [hz]
            ring
      _ = (∫ x, (f x) ^ 2 ∂m) * ∫ y, (g y) ^ 2 ∂n := by
            exact integral_prod_mul (L := ℝ) (fun x => (f x) ^ 2) (fun y => (g y) ^ 2)
      _ = ‖f‖ ^ 2 * ‖g‖ ^ 2 := by rw [integral_sq_eq_norm_sq, integral_sq_eq_norm_sq]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, ← h2, integral_sq_eq_norm_sq]

private theorem norm_tensorLp_le_rpow {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n]
    (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) {μ : ℝ} (hμ : 0 < μ)
    {C C' γ₁ γ₂ : ℝ} (hC : 0 ≤ C)
    (hf : ‖f‖ ≤ C * μ ^ γ₁) (hg : ‖g‖ ≤ C' * μ ^ (γ₂ - 1)) :
    ‖tensorLp f g‖ ≤ (C * C') * μ ^ (γ₁ + γ₂ - 1) := by
  rw [norm_tensorLp]
  rw [show γ₁ + γ₂ - 1 = γ₁ + (γ₂ - 1) by ring, Real.rpow_add hμ]
  calc
    ‖f‖ * ‖g‖ ≤ (C * μ ^ γ₁) * (C' * μ ^ (γ₂ - 1)) :=
      mul_le_mul hf hg (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hμ.le _))
    _ = _ := by ring

/-- If the same singular values satisfy the
interpolation-output bounds `‖fᵢ‖ ≤ C μᵢ^γ₁` and `‖gᵢ‖ ≤ C' μᵢ^(γ₂−1)`, then the tensor
summands are summable in `L²` whenever `∑ μᵢ^(γ₁+γ₂−1)` converges. -/
theorem tensor_norm_summable_of_rpow_bounds {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n] {ι : Type*}
    (f : ι → Lp ℝ 2 m) (g : ι → Lp ℝ 2 n) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (C C' γ₁ γ₂ : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C * μ i ^ γ₁) (hg : ∀ i, ‖g i‖ ≤ C' * μ i ^ (γ₂ - 1))
    (hsum : Summable fun i => μ i ^ (γ₁ + γ₂ - 1)) :
    Summable fun i => ‖tensorLp (f i) (g i)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i =>
    norm_tensorLp_le_rpow (f i) (g i) (hμ i) hC (hf i) (hg i)) (hsum.mul_left (C * C'))

/-- Triangle inequality for the actual tensor sum with the spectral majorant. -/
theorem norm_tsum_tensorLp_le_power_sum
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n] {ι : Type*}
    (f : ι → Lp ℝ 2 m) (g : ι → Lp ℝ 2 n) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (C C' γ₁ γ₂ : ℝ) (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C * μ i ^ γ₁) (hg : ∀ i, ‖g i‖ ≤ C' * μ i ^ (γ₂ - 1))
    (hsum : Summable fun i => μ i ^ (γ₁ + γ₂ - 1)) :
    ‖∑' i, tensorLp (f i) (g i)‖ ≤ (C * C') * ∑' i, μ i ^ (γ₁ + γ₂ - 1) := by
  have hterm (i : ι) := norm_tensorLp_le_rpow (f i) (g i) (hμ i) hC (hf i) (hg i)
  have hnorm := tensor_norm_summable_of_rpow_bounds f g μ hμ C C' γ₁ γ₂ hC hf hg hsum
  calc
    _ ≤ ∑' i, ‖tensorLp (f i) (g i)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, (C * C') * μ i ^ (γ₁ + γ₂ - 1) := hnorm.tsum_le_tsum hterm (hsum.mul_left _)
    _ = _ := tsum_mul_left

/-- A finite sum of tensor classes is a.e. the pointwise finite cross sum, the form
consumed by the native finite-product L2 limit theorem. -/
theorem tensorLp_finset_sum_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite n] {ι : Type*} (s : Finset ι)
    (f : ι → Lp ℝ 2 m) (g : ι → Lp ℝ 2 n) :
    ((∑ i ∈ s, tensorLp (f i) (g i) : Lp ℝ 2 (m.prod n)) : α × β → ℝ) =ᵐ[m.prod n]
      fun z => ∑ i ∈ s, f i z.1 * g i z.2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := m.prod n)] with z hz
    rw [hz, Pi.zero_apply]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (tensorLp (f i) (g i)) (∑ j ∈ s, tensorLp (f j) (g j)),
      tensorLp_ae (f i) (g i), ih] with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]

/-- C3-D10e: an arbitrary-index `HasSum` yields a genuine Nat-indexed sequence of actual finite
partial sums converging to the same limit (no enumeration of the index type is imposed). -/
theorem exists_finset_seq_tendsto_of_hasSum {ι E : Type*} [NormedAddCommGroup E]
    (v : ι → E) (S : E) (h : HasSum v S) :
    ∃ s : ℕ → Finset ι, Tendsto (fun k => ∑ i ∈ s k, v i) atTop (𝓝 S) := by
  have hk : ∀ k : ℕ, ∃ t : Finset ι, dist (∑ i ∈ t, v i) S < 1 / ((k : ℝ) + 1) := fun k =>
    (Filter.Tendsto.eventually h (Metric.ball_mem_nhds S (by positivity))).exists
  choose s hs using hk
  refine ⟨s, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun k => dist_nonneg) (fun k => (hs k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat


/-- Faster-than-polynomial singular-value decay makes every positive
power of the singular values summable. -/
theorem summable_singular_powers {μ : ℕ → ℝ} (hμ : ∀ j, 0 ≤ μ j)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ j : ℕ, μ j ≤ C * ((j : ℝ) + 1) ^ (-(N : ℝ)))
    {κ : ℝ} (hκ : 0 < κ) : Summable (fun j => μ j ^ κ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / κ)
  have hpow : -(N : ℝ) * κ < -1 := by
    have hN' := (div_lt_iff₀ hκ).mp hN
    nlinarith
  obtain ⟨C, hC, hbound⟩ := hdecay N
  have hs : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-(N : ℝ) * κ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun j : ℕ => (j : ℝ) ^ (-(N : ℝ) * κ)) 1).mpr
        (Real.summable_nat_rpow.mpr hpow)
  refine Summable.of_nonneg_of_le (fun j => Real.rpow_nonneg (hμ j) κ) ?_
    (hs.mul_left (C ^ κ))
  intro j
  have hj : 0 ≤ (j : ℝ) + 1 := by positivity
  calc
    _ ≤ (C * ((j : ℝ) + 1) ^ (-(N : ℝ))) ^ κ :=
      Real.rpow_le_rpow (hμ j) (hbound j) hκ.le
    _ = _ := by rw [Real.mul_rpow hC.le (Real.rpow_nonneg hj _), ← Real.rpow_mul hj]

end LocalMetricExtension
