module

public import Proof.CalderonPatch.HomogeneousTests

import Mathlib.Tactic.Ring
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.SmallJetBounds

@[expose] public section

noncomputable section
open Filter Metric MvPolynomial Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace CalderonPatch

open CalderonN (I X Mat axis chartPartial chartDerivativeWord chartDerivativeWord_sorted
  sortedChartWord sortedChartWord_count)

variable {n : ℕ}

private theorem sortedChartWord_length (a : I n →₀ ℕ) : (sortedChartWord a).length = a.degree := by
  have hSupp : (sortedChartWord a).toFinset = a.support := by
    ext i
    rw [List.mem_toFinset, ← List.count_pos_iff, sortedChartWord_count, Finsupp.mem_support_iff]
    omega
  rw [← List.sum_toFinset_count_eq_length, hSupp]
  simp only [sortedChartWord_count]
  rfl

private theorem sortedChartWord_product (a : I n →₀ ℕ) (ξ : I n → ℝ) :
    ((sortedChartWord a).map ξ).prod = a.prod (fun i k => ξ i ^ k) := by
  rw [Finset.prod_list_map_count]
  simp only [sortedChartWord_count, Finsupp.prod]
  congr 1
  ext i
  rw [List.mem_toFinset, ← List.count_pos_iff, sortedChartWord_count, Finsupp.mem_support_iff]
  omega

/-- A scalar second-order differential operator in an interior chart. -/
def coordinateElliptic (A : X n → Mat n) (b : X n → I n → ℝ) (f : X n → ℝ) : X n → ℝ :=
  (∑ i : I n, ∑ j : I n, (fun x => A x i j) * chartDerivativeWord [i, j] f) +
    ∑ i : I n, (fun x => b x i) * chartDerivativeWord [i] f

private theorem chartPartial_elliptic_linear_pow {A : X n → Mat n} {b : X n → I n → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) (hb : ∀ i, ContDiff ℝ ∞ (fun x => b x i))
    {f : X n → ℝ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (a : I n →₀ ℕ) (ha : a.degree ≤ k)
    (l : X n →L[ℝ] ℝ) (h : f =ᶠ[𝓝 0] fun x => (l x) ^ (k + 2)) :
    chartPartial a (coordinateElliptic A b f) 0 =
      if a.degree = k then (↑(k + 2).factorial : ℝ) * a.prod (fun i e => (l (axis i)) ^ e) *
        eval (fun i => l (axis i)) (ellipticQuadraticSymbol (A 0)) else 0 := by
  let W := sortedChartWord a
  have hW : W.length = a.degree := sortedChartWord_length a
  let u (i j : I n) : X n → ℝ := (fun x => A x i j) * chartDerivativeWord [i,j] f
  let v (i : I n) : X n → ℝ := (fun x => b x i) * chartDerivativeWord [i] f
  have hu (i j : I n) : ContDiff ℝ ∞ (u i j) := (hA i j).mul (CalderonN.contDiff_chartDerivativeWord [i,j] hf)
  have hv (i : I n) : ContDiff ℝ ∞ (v i) := (hb i).mul (CalderonN.contDiff_chartDerivativeWord [i] hf)
  have huSum (i : I n) : ContDiff ℝ ∞ (∑ j : I n, u i j) := by
    change ContDiff ℝ ∞ (fun x => (∑ j : I n, u i j) x)
    simpa only [Finset.sum_apply] using ContDiff.sum (s := Finset.univ) (fun j _ => hu i j)
  have hU : ContDiff ℝ ∞ (∑ i : I n, ∑ j : I n, u i j) := by
    change ContDiff ℝ ∞ (fun x => (∑ i : I n, ∑ j : I n, u i j) x)
    simpa only [Finset.sum_apply] using ContDiff.sum (s := Finset.univ) (fun i _ => huSum i)
  have hV : ContDiff ℝ ∞ (∑ i : I n, v i) := by
    change ContDiff ℝ ∞ (fun x => (∑ i : I n, v i) x)
    simpa only [Finset.sum_apply] using ContDiff.sum (s := Finset.univ) (fun i _ => hv i)
  rw [← chartDerivativeWord_sorted]
  change chartDerivativeWord W ((∑ i : I n, ∑ j : I n, u i j) + ∑ i : I n, v i) 0 = _
  rw [chartDerivativeWord_add W hU hV, chartDerivativeWord_sum _ W _ (fun i _ => huSum i),
    chartDerivativeWord_sum _ W _ (fun i _ => hv i)]
  simp_rw [chartDerivativeWord_sum _ W (u _) (fun j _ => hu _ j)]
  have hV₀ (i : I n) : chartDerivativeWord W (v i) 0 = 0 := by
    have hh := chartDerivativeWord_coeff_of_linear_pow_germ W [i] (hb i) hf
      (by rw [hW]; simp; omega) l h
    simpa only [v, List.length_singleton, hW, ite_eq_right (show a.degree + 1 ≠ k + 2 by omega)] using hh
  have hU₀ (i j : I n) : chartDerivativeWord W (u i j) 0 =
      if a.degree = k then (↑(k + 2).factorial : ℝ) * a.prod (fun i e => (l (axis i)) ^ e) *
        (A 0 i j * l (axis i) * l (axis j)) else 0 := by
    have hh := chartDerivativeWord_coeff_of_linear_pow_germ W [i,j] (hA i j) hf
      (by rw [hW]; simp; omega) l h
    simpa only [u, List.length_cons, List.length_nil, Nat.zero_add, hW, Nat.add_right_cancel_iff,
      List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, one_mul, sortedChartWord_product, W, mul_assoc, mul_comm, mul_left_comm] using hh
  simp only [Pi.add_apply, Finset.sum_apply, hU₀, hV₀, Finset.sum_const_zero, add_zero,
    ellipticQuadraticSymbol, map_sum, map_mul, eval_C, eval_X]
  by_cases hk : a.degree = k
  · simp only [hk, ite_true, Finset.mul_sum]
  · simp only [ite_eq_right hk, Finset.sum_const_zero]

private theorem pointSymbolApply_germ {f g : X n → ℝ} (h : f =ᶠ[𝓝 0] g) (P : MvPolynomial (I n) ℝ) :
    pointSymbolApply f P = pointSymbolApply g P := by
  rw [pointSymbolApply_sum_coeff, pointSymbolApply_sum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  rw [← chartDerivativeWord_sorted, ← chartDerivativeWord_sorted]
  exact congrArg (P.coeff a * ·) (chartDerivativeWord_congr_germ (sortedChartWord a) h).eq_of_nhds

private theorem pointSymbolApply_elliptic_linear_pow {A : X n → Mat n} {b : X n → I n → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) (hb : ∀ i, ContDiff ℝ ∞ (fun x => b x i))
    {f : X n → ℝ} (hf : ContDiff ℝ ∞ f) (P : MvPolynomial (I n) ℝ)
    (l : X n →L[ℝ] ℝ) (h : f =ᶠ[𝓝 0] fun x => (l x) ^ (P.totalDegree + 2)) :
    pointSymbolApply (coordinateElliptic A b f) P = (↑(P.totalDegree + 2).factorial : ℝ) *
      eval (fun i => l (axis i)) (homogeneousComponent P.totalDegree P * ellipticQuadraticSymbol (A 0)) := by
  let k := P.totalDegree
  let ξ (i : I n) := l (axis i)
  let q := eval ξ (ellipticQuadraticSymbol (A 0))
  rw [pointSymbolApply_sum_coeff]
  change ∑ a ∈ P.support, P.coeff a * chartPartial a (coordinateElliptic A b f) 0 = _
  calc
    _ = ∑ a ∈ P.support with a.degree = k,
        P.coeff a * ((↑(k + 2).factorial : ℝ) * a.prod (fun i e => ξ i ^ e) * q) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      rw [chartPartial_elliptic_linear_pow hA hb hf a (le_totalDegree ha) l h, mul_ite, mul_zero]
    _ = _ := by
      rw [map_mul, homogeneousComponent_apply, map_sum]
      simp only [eval_monomial]
      change _ = (↑(k + 2).factorial : ℝ) *
        ((∑ a ∈ P.support with a.degree = k, P.coeff a * a.prod (fun i e => ξ i ^ e)) * q)
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring

private theorem homogeneousComponent_top_ne_zero {P : MvPolynomial (I n) ℝ} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  obtain ⟨a, ha, hdeg⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hP) (fun a => a.degree)
  change P.totalDegree = a.degree at hdeg
  intro h
  have hh := congrArg (fun Q : MvPolynomial (I n) ℝ => Q.coeff a) h
  change (homogeneousComponent P.totalDegree P).coeff a = (0 : MvPolynomial (I n) ℝ).coeff a at hh
  rw [coeff_homogeneousComponent, ite_eq_left hdeg.symm] at hh
  exact (mem_support_iff.mp ha) (by simpa using hh)

/-- If the image of a point-supported distribution under an elliptic
second-order operator has order at most two, the distribution itself is
a multiple of point evaluation. Pure homogeneous test germs detect the
top coefficient polynomial and exclude cancellation by lower terms. -/
theorem compactTest_point_support_elliptic_order [NeZero n] {K : Compacts (X n)}
    (hK : (K : Set (X n)) ∈ 𝓝 0) (T : 𝓓_{K}(X n, ℝ) →L[ℝ] ℝ)
    (hT : ∀ f : 𝓓_{K}(X n, ℝ), (f : X n → ℝ) =ᶠ[𝓝 0] 0 → T f = 0)
    (L : 𝓓_{K}(X n, ℝ) → 𝓓_{K}(X n, ℝ)) {A : X n → Mat n} {b : X n → I n → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) (hb : ∀ i, ContDiff ℝ ∞ (fun x => b x i))
    (hPos : (A 0).PosDef)
    (hL : ∀ f, (L f : X n → ℝ) =ᶠ[𝓝 0] coordinateElliptic A b f)
    (hSmall : ∀ f : 𝓓_{K}(X n, ℝ), (∀ j ≤ 2, iteratedFDeriv ℝ j f 0 = 0) → T (L f) = 0) :
    ∃ c : ℝ, ∀ f : 𝓓_{K}(X n, ℝ), T f = c * f 0 := by
  obtain ⟨P, hP⟩ := exists_pointSymbol_of_point_support T hK hT
  have hd : P.totalDegree = 0 := by
    by_contra hd
    have hP₀ : P ≠ 0 := by rintro rfl; exact hd totalDegree_zero
    let S := homogeneousComponent P.totalDegree P * ellipticQuadraticSymbol (A 0)
    have hS := mul_ne_zero (homogeneousComponent_top_ne_zero hP₀) (ellipticQuadraticSymbol_ne_zero hPos)
    have hSh : S.IsHomogeneous (P.totalDegree + 2) :=
      (homogeneousComponent_isHomogeneous _ _).mul (ellipticQuadraticSymbol_homogeneous _)
    obtain ⟨ξ, hξ⟩ : ∃ ξ : I n → ℝ, eval ξ S ≠ 0 := by
      by_contra h
      push Not at h
      exact hS (hSh.eq_zero_of_forall_eval_eq_zero h)
    let l : X n →L[ℝ] ℝ := ∑ i : I n, ξ i • EuclideanSpace.proj i
    have hl : (fun i => l (axis i)) = ξ := by
      funext i
      simp only [l, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      change (∑ j : I n, ξ j * (axis i) j) = ξ i
      simp only [axis, PiLp.single_apply, mul_ite, mul_one, mul_zero]
      simp [Finset.sum_ite_eq']
    obtain ⟨f, hf⟩ := exists_compactTest_germ hK (l.contDiff.pow (P.totalDegree + 2))
    have h := hSmall f (fun j hj => iteratedFDeriv_zero_of_linear_pow_germ f.contDiff
      (show j < P.totalDegree + 2 by omega) l hf)
    rw [hP, pointSymbolApply_germ (hL f), pointSymbolApply_elliptic_linear_pow hA hb f.contDiff P l hf, hl] at h
    exact (mul_ne_zero (by positivity) hξ) h
  have hc := totalDegree_eq_zero_iff_eq_C.mp hd
  refine ⟨P.coeff 0, fun f => ?_⟩
  rw [hP]
  conv_lhs => rw [hc]
  change pointSymbolApply f (MvPolynomial.monomial 0 (P.coeff 0)) = _
  rw [pointSymbolApply_monomial]
  change _ * chartPartial (fun _ => 0) f 0 = _
  rw [CalderonN.chartPartial_zero]

end CalderonPatch
