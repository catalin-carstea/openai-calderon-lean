module

public import Proof.CalderonN.HarmonicSeries
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

import Proof.CalderonN.DilationHarmonic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem norm_jet_comp_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {L : E →L[ℝ] F} (hL : ‖L‖ ≤ 1)
    {f : F → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (i := k) (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_one ‖iteratedFDeriv ℝ k f (L x)‖]
  simp only [mul_one]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg L) hL (n := k))
    (norm_nonneg (iteratedFDeriv ℝ k f (L x)))

/-- Products of two smooth families are normally summable on the product
when each derivative costs a fixed multiple of the corresponding weight. -/
theorem contDiff_tsum_tensor_of_global_jets {ι : Type*}
    {f b : ι → (X dim) → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    {a c : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (_hc : ∀ i, 0 ≤ c i)
    {A C : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) (_hC : ∀ k, 0 ≤ C k)
    (hFa : ∀ k i x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A k * a i)
    (hBc : ∀ k i x, ‖iteratedFDeriv ℝ k (b i) x‖ ≤ C k * c i)
    (hsum : Summable (fun i => a i * c i)) :
    ContDiff ℝ ∞ (fun q : (X dim) × (X dim) => ∑' i, f i q.1 * b i q.2) := by
  let M (k : ℕ) := ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ) * A j * C (k-j)
  let p₁ := ContinuousLinearMap.fst ℝ (X dim) (X dim)
  let p₂ := ContinuousLinearMap.snd ℝ (X dim) (X dim)
  have hF (i : ι) : ContDiff ℝ ∞ (f i ∘ p₁) := (hf i).comp contDiff_fst
  have hB (i : ι) : ContDiff ℝ ∞ (b i ∘ p₂) := (hb i).comp contDiff_snd
  apply contDiff_tsum (v := fun k i => M k * (a i * c i))
  · exact fun i => (hF i).mul (hB i)
  · exact fun k _ => hsum.mul_left (M k)
  · intro k i x hk
    refine (norm_iteratedFDeriv_mul_le (hF i) (hB i) x (n := k) (by simp)).trans ?_
    rw [show M k = _ from rfl, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have h₁ := (norm_jet_comp_le (ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := (X dim)) (F := (X dim)))
      (hf i) j x).trans (hFa j i x.1)
    have h₂ := (norm_jet_comp_le (ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := (X dim)) (F := (X dim)))
      (hb i) (k-j) x).trans (hBc (k-j) i x.2)
    calc
      _ ≤ (k.choose j : ℝ) * (A j * a i) * (C (k-j) * c i) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _)) h₂
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA j) (ha i)))
      _ = _ := by ring

/-- At a point where every summand is harmonic, the weighted normal series
is harmonic at the same point. -/
theorem laplace_tsum_mul_eq_zero_of_global_jets {ι : Type*}
    {f : ι → (X dim) → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {a c q : ι → ℝ} (_ha : ∀ i, 0 ≤ a i) (hq : ∀ i, ‖q i‖ ≤ c i)
    {A : ℕ → ℝ} (_hA : ∀ k, 0 ≤ A k)
    (hFa : ∀ k i x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A k * a i)
    (hsum : Summable (fun i => a i * c i))
    (g : (MetricField dim)) (x : (X dim)) (hLap : ∀ i, laplace g (f i) x = 0) :
    laplace g (fun y => ∑' i, q i * f i y) x = 0 := by
  have hfi (i : ι) : ContDiff ℝ ∞ (fun y => q i * f i y) :=
    contDiff_const.mul (hf i)
  have hj (k : ℕ) (i : ι) (y : (X dim)) :
      ‖iteratedFDeriv ℝ k (fun y => q i * f i y) y‖ ≤ A k * (a i * c i) := by
    have hd : ContDiffAt ℝ (k : ℕ∞ω) (f i) y :=
      (hf i).contDiffAt.of_le (by simp)
    rw [show (fun y => q i * f i y) = (fun y => q i • f i y) by funext y; rfl,
      iteratedFDeriv_const_smul_apply' hd, norm_smul]
    calc
      _ ≤ c i * (A k * a i) :=
        mul_le_mul (hq i) (hFa k i y) (norm_nonneg _) ((norm_nonneg _).trans (hq i))
      _ = _ := by ring
  have h := hasSum_laplace_of_uniform_jets hfi (fun k i => A k * (a i * c i))
    (fun k => hsum.mul_left (A k)) hj g x
  have hz (i : ι) : laplace g (fun y => q i * f i y) x = 0 := by
    rw [laplace_const_mul isOpen_univ (hf i).contDiffOn (mem_univ x) g (q i), hLap i, mul_zero]
  simp only [hz] at h
  exact h.unique hasSum_zero

end CalderonN
