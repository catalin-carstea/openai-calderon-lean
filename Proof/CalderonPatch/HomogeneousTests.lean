module

public import Proof.CalderonPatch.PointSymbols
public import Proof.CalderonN.ChartSchwarzWords

import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Filter Metric Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace CalderonPatch

open CalderonN (I X axis coordDeriv chartPartial chartDerivativeWord chartDerivativeWord_sorted
  chartDerivativeWord_ofFn contDiff_chartDerivativeWord norm_multilinear_le_of_chart_components
  sortedChartWord)

variable {n : ℕ}

theorem chartDerivativeWord_append (L W : List (I n)) (f : X n → ℝ) :
    chartDerivativeWord (L ++ W) f = chartDerivativeWord L (chartDerivativeWord W f) :=
  List.foldr_append

theorem chartDerivativeWord_congr_germ (L : List (I n)) {f g : X n → ℝ} {q : X n}
    (h : f =ᶠ[𝓝 q] g) : chartDerivativeWord L f =ᶠ[𝓝 q] chartDerivativeWord L g := by
  induction L with
  | nil => exact h
  | cons i L ih =>
    simpa only [chartDerivativeWord, List.foldr_cons, coordDeriv, Filter.EventuallyEq] using
      ih.fderiv.mono (fun x hx => congrFun (congrArg DFunLike.coe hx) (axis i))

theorem chartDerivativeWord_add (L : List (I n)) {f g : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    chartDerivativeWord L (f + g) = chartDerivativeWord L f + chartDerivativeWord L g := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    change coordDeriv i (chartDerivativeWord L (f + g)) = _
    rw [ih]
    funext x
    change fderiv ℝ (chartDerivativeWord L f + chartDerivativeWord L g) x (axis i) =
      fderiv ℝ (chartDerivativeWord L f) x (axis i) + fderiv ℝ (chartDerivativeWord L g) x (axis i)
    rw [fderiv_add ((contDiff_chartDerivativeWord L hf).differentiable (by simp) x)
      ((contDiff_chartDerivativeWord L hg).differentiable (by simp) x), ContinuousLinearMap.add_apply]

theorem chartDerivativeWord_sum {α : Type*} (s : Finset α) (L : List (I n)) (f : α → X n → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) :
    chartDerivativeWord L (∑ i ∈ s, f i) = ∑ i ∈ s, chartDerivativeWord L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    clear hf
    induction L with
    | nil => rfl
    | cons i L ih => change coordDeriv i (chartDerivativeWord L 0) = 0; rw [ih]; ext; simp [coordDeriv]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, chartDerivativeWord_add,
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
    · exact hf i (Finset.mem_insert_self _ _)
    · change ContDiff ℝ ∞ (fun x => (∑ j ∈ s, f j) x)
      simpa only [Finset.sum_apply] using ContDiff.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem coordDeriv_mul (i : I n) {f g : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    coordDeriv i (f * g) = coordDeriv i f * g + f * coordDeriv i g := by
  funext x
  simp only [coordDeriv, fderiv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x),
    Pi.add_apply, Pi.mul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

private theorem contDiff_coordDeriv (i : I n) {f : X n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coordDeriv i f) := contDiff_chartDerivativeWord [i] hf

/-- When the lower-order derivatives of the second factor vanish at a point,
only the term placing every derivative on that factor survives. -/
theorem chartDerivativeWord_mul_of_lower_zero (L : List (I n)) {q : X n}
    {f g : X n → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ W : List (I n), W.length < L.length → chartDerivativeWord W g q = 0) :
    chartDerivativeWord L (f * g) q = f q * chartDerivativeWord L g q := by
  induction L using List.reverseRecOn generalizing f g with
  | nil => rfl
  | append_singleton L i ih =>
    simp only [chartDerivativeWord_append]
    change chartDerivativeWord L (coordDeriv i (f * g)) q = f q * chartDerivativeWord L (coordDeriv i g) q
    have hLeft : ContDiff ℝ ∞ (coordDeriv i f * g) := (contDiff_coordDeriv i hf).mul hg
    have hRight : ContDiff ℝ ∞ (f * coordDeriv i g) := hf.mul (contDiff_coordDeriv i hg)
    rw [coordDeriv_mul i hf hg, chartDerivativeWord_add L hLeft hRight, Pi.add_apply,
      ih (contDiff_coordDeriv i hf) hg (fun W hW => hzero W (by simp; omega)),
      ih hf (contDiff_coordDeriv i hg) (fun W hW => by
        have h := hzero (W ++ [i]) (by simp; omega)
        rwa [chartDerivativeWord_append] at h),
      hzero L (by simp), mul_zero, zero_add]

/-- Ordinary derivatives of a power of a linear coordinate. -/
theorem chartDerivativeWord_linear_pow (L : List (I n)) (N : ℕ) (l : X n →L[ℝ] ℝ) :
    chartDerivativeWord L (fun x => (l x) ^ N) = fun x =>
      ((N.descFactorial L.length : ℕ) : ℝ) * (l x) ^ (N - L.length) *
        (L.map (fun i => l (axis i))).prod := by
  induction L with
  | nil => simp [chartDerivativeWord]
  | cons i L ih =>
    change coordDeriv i (chartDerivativeWord L (fun x => (l x) ^ N)) = _
    rw [ih]
    funext x
    change fderiv ℝ (fun y => (N.descFactorial L.length : ℝ) * l y ^ (N - L.length) *
      (L.map (fun k => l (axis k))).prod) x (axis i) = _
    rw [fderiv_mul_const (by fun_prop), fderiv_const_mul (by fun_prop),
      fderiv_fun_pow _ l.differentiableAt, l.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, List.length_cons,
      List.map_cons, List.prod_cons, Nat.descFactorial_succ, Nat.cast_mul]
    have hpow : N - L.length - 1 = N - (L.length + 1) := by omega
    rw [hpow]
    ring

theorem chartDerivativeWord_linear_pow_at_zero (L : List (I n)) (N : ℕ) (l : X n →L[ℝ] ℝ) :
    chartDerivativeWord L (fun x => (l x) ^ N) 0 =
      if L.length = N then (N.factorial : ℝ) * (L.map (fun i => l (axis i))).prod else 0 := by
  rw [chartDerivativeWord_linear_pow]
  simp only [map_zero]
  rcases lt_trichotomy L.length N with h | h | h
  · simp [h.ne, zero_pow (Nat.sub_ne_zero_of_lt h)]
  · simp [h, Nat.descFactorial_self]
  · simp [h.ne', Nat.descFactorial_eq_zero_iff_lt.mpr h]

/-- Multiply a smooth function by a bump equal to one near the origin
to obtain a test in the fixed compact neighborhood. -/
theorem exists_compactTest_germ {K : Compacts (X n)} (hK : (K : Set (X n)) ∈ 𝓝 0)
    {u : X n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∃ f : 𝓓_{K}(X n, ℝ), (f : X n → ℝ) =ᶠ[𝓝 0] u := by
  obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp hK
  let χ : ContDiffBump (0 : X n) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hχ : tsupport (χ : X n → ℝ) ⊆ K := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (show r / 2 < r by linarith)).trans hrK
  let f : 𝓓_{K}(X n, ℝ) := ⟨fun x => χ x * u x,
    χ.contDiff.mul hu, fun x hx => by
      change χ x * u x = 0
      rw [image_eq_zero_of_notMem_tsupport (fun hc => hx (hχ hc)), zero_mul]⟩
  refine ⟨f, ?_⟩
  filter_upwards [χ.eventuallyEq_one] with x hx
  change χ x = 1 at hx
  change χ x * u x = u x
  rw [hx, one_mul]

/-- The whole Fréchet jet below the degree of a homogeneous test vanishes. -/
theorem iteratedFDeriv_zero_of_linear_pow_germ [NeZero n] {f : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) {N j : ℕ} (hj : j < N) (l : X n →L[ℝ] ℝ)
    (h : f =ᶠ[𝓝 0] (fun x => (l x) ^ N)) : iteratedFDeriv ℝ j f 0 = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [mul_zero] using norm_multilinear_le_of_chart_components (iteratedFDeriv ℝ j f 0) 0
    le_rfl (fun idx => by
      rw [← congrFun (chartDerivativeWord_ofFn j idx hf) 0]
      have hh := (chartDerivativeWord_congr_germ (List.ofFn idx) h).eq_of_nhds
      rw [hh, chartDerivativeWord_linear_pow_at_zero, List.length_ofFn, ite_eq_right hj.ne, abs_zero])

/-- The principal term of a derivative word applied to one coefficient times
another derivative word, when the input germ is a homogeneous test. -/
theorem chartDerivativeWord_coeff_of_linear_pow_germ
    (L W : List (I n)) {a f : X n → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    {N : ℕ} (hN : L.length + W.length ≤ N) (l : X n →L[ℝ] ℝ)
    (h : f =ᶠ[𝓝 0] (fun x => (l x) ^ N)) :
    chartDerivativeWord L (a * chartDerivativeWord W f) 0 =
      if L.length + W.length = N then
        a 0 * ((N.factorial : ℝ) * ((L ++ W).map (fun i => l (axis i))).prod) else 0 := by
  rw [chartDerivativeWord_mul_of_lower_zero L ha (contDiff_chartDerivativeWord W hf),
    ← chartDerivativeWord_append, (chartDerivativeWord_congr_germ (L ++ W) h).eq_of_nhds,
    chartDerivativeWord_linear_pow_at_zero, List.length_append, mul_ite, mul_zero]
  intro U hU
  rw [← chartDerivativeWord_append, (chartDerivativeWord_congr_germ (U ++ W) h).eq_of_nhds,
    chartDerivativeWord_linear_pow_at_zero, List.length_append, ite_eq_right (show U.length + W.length ≠ N by omega)]

end CalderonPatch
