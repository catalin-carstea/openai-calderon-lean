module

public import Proof.CalderonPatch.HomogeneousTests
public import Mathlib.Geometry.Manifold.Instances.Real

import Mathlib.Tactic
import Proof.CalderonN.CompactSmoothExtension

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X axis coordDeriv chartDerivativeWord contDiff_chartDerivativeWord
  chartDerivativeWord_perm chartDerivativeWord_ofFn norm_multilinear_le_of_chart_components)

variable {n : ℕ} {U : Set (X n)} {i : I n}

/-- The flat seam of a chart, localized to the given open domain. -/
@[expose] def boundaryFace (U : Set (X n)) (i : I n) : Set (X n) := U ∩ {x | x i = 0}

private theorem coordDeriv_tangential_eqOn_zero (hU : IsOpen U) {j : I n} (hji : j ≠ i)
    {f : X n → ℝ} (hf : ContDiff ℝ ∞ f) (h : EqOn f 0 (boundaryFace U i)) :
    EqOn (coordDeriv j f) 0 (boundaryFace U i) := by
  intro x hx
  let c : ℝ → X n := fun t => x + t • axis j
  have hc : HasDerivAt c (axis j) 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (axis j)).const_add x
  have hc₀ : c 0 = x := by simp [c]
  have hNear : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U :=
    hc.continuousAt.eventually_mem (hc₀.symm ▸ hU.mem_nhds hx.1)
  have hZero : (fun t => f (c t)) =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
    filter_upwards [hNear] with t ht
    have hx₀ : x i = 0 := hx.2
    exact h ⟨ht, by change (x + t • axis j) i = 0; simp [axis, hji, hx₀]⟩
  have hd := ((hf.differentiable (by simp) (c 0)).hasFDerivAt).comp_hasDerivAt 0 hc
  have hd' := (hd.congr_of_eventuallyEq hZero.symm).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  exact hc₀ ▸ hd'

private theorem chartDerivativeWord_tangential_eqOn_zero (hU : IsOpen U) {f : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) (h : EqOn f 0 (boundaryFace U i)) (L : List (I n))
    (hL : ∀ j ∈ L, j ≠ i) : EqOn (chartDerivativeWord L f) 0 (boundaryFace U i) := by
  induction L with
  | nil => exact h
  | cons j L ih =>
    change EqOn (coordDeriv j (chartDerivativeWord L f)) 0 (boundaryFace U i)
    exact coordDeriv_tangential_eqOn_zero hU (hL j List.mem_cons_self)
      (contDiff_chartDerivativeWord L hf) (ih fun k hk => hL k (List.mem_cons_of_mem _ hk))

private theorem chartDerivativeWord_eqOn_zero_from_normal (hU : IsOpen U) {f : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) (L : List (I n))
    (h : EqOn (chartDerivativeWord (List.replicate (L.count i) i) f) 0 (boundaryFace U i)) :
    EqOn (chartDerivativeWord L f) 0 (boundaryFace U i) := by
  let W := L.filter (· != i)
  let N := List.replicate (L.count i) i
  have hP : L.Perm (W ++ N) := by
    apply List.perm_iff_count.mpr
    intro j
    by_cases hj : j = i
    · subst j
      have hNot : i ∉ W := fun hm => by simpa [W] using (List.mem_filter.mp hm).2
      simp [N, List.count_eq_zero.mpr hNot]
    · simp [W, N, List.count_filter, List.count_replicate, hj, Ne.symm hj]
  rw [chartDerivativeWord_perm hP hf, chartDerivativeWord_append]
  exact chartDerivativeWord_tangential_eqOn_zero hU (contDiff_chartDerivativeWord N hf) h W
    (fun j hj => by simpa [W] using (List.mem_filter.mp hj).2)

theorem boundaryFace_subset_closure_positive (hU : IsOpen U) :
    boundaryFace U i ⊆ closure (U ∩ {x : X n | 0 < x i}) := by
  intro x hx
  have hx' : x ∈ closure ({y : X n | 0 < y i}) := by
    rw [closure_open_halfSpace]
    exact le_of_eq hx.2.symm
  rw [mem_closure_iff_frequently]
  exact ((mem_closure_iff_frequently.mp hx').and_eventually (hU.mem_nhds hx.1)).mono
    (fun _ h => ⟨h.2, h.1⟩)

/-- Pure normal jets vanishing as functions along an open face imply
vanishing of all mixed jets there. -/
theorem iteratedFDeriv_eq_zero_of_pure_normal_jets [NeZero n] (hU : IsOpen U)
    {u : X n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hNormal : ∀ k, EqOn (chartDerivativeWord (List.replicate k i) u) 0 (boundaryFace U i)) :
    ∀ x ∈ boundaryFace U i, ∀ k, iteratedFDeriv ℝ k u x = 0 := by
  intro x hx k
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [mul_zero] using norm_multilinear_le_of_chart_components (iteratedFDeriv ℝ k u x) 0
    le_rfl (fun idx => by
      rw [← congrFun (chartDerivativeWord_ofFn k idx hu) x]
      have h := chartDerivativeWord_eqOn_zero_from_normal hU hu (List.ofFn idx)
        (hNormal ((List.ofFn idx).count i)) hx
      rw [h, Pi.zero_apply, abs_zero])

private theorem chartDerivativeWord_sub (L : List (I n)) {u v : X n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    chartDerivativeWord L (u - v) = chartDerivativeWord L u - chartDerivativeWord L v := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    change coordDeriv j (chartDerivativeWord L (u - v)) = _
    rw [ih]
    funext x
    change fderiv ℝ (chartDerivativeWord L u - chartDerivativeWord L v) x (axis j) = _
    rw [fderiv_sub ((contDiff_chartDerivativeWord L hu).differentiable (by simp) x)
      ((contDiff_chartDerivativeWord L hv).differentiable (by simp) x)]
    rfl

/-- Equality of the pure normal jets along a common boundary face
gives the full signed jets required for smooth cap attachment. -/
theorem iteratedFDeriv_eqOn_of_pure_normal_jets [NeZero n] (hU : IsOpen U)
    {u v : X n → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hNormal : ∀ k, EqOn (chartDerivativeWord (List.replicate k i) u)
      (chartDerivativeWord (List.replicate k i) v) (boundaryFace U i)) :
    ∀ k, EqOn (iteratedFDeriv ℝ k u) (iteratedFDeriv ℝ k v) (boundaryFace U i) := by
  have hZero (k : ℕ) : EqOn (chartDerivativeWord (List.replicate k i) (u - v)) 0 (boundaryFace U i) := by
    intro x hx
    rw [chartDerivativeWord_sub _ hu hv, Pi.sub_apply, hNormal k hx, sub_self]
    rfl
  intro k x hx
  have h := iteratedFDeriv_eq_zero_of_pure_normal_jets hU (hu.sub hv) hZero x hx k
  change iteratedFDeriv ℝ k (u - v) x = 0 at h
  rw [iteratedFDeriv_sub_apply (hu.contDiffAt.of_le (by simp)) (hv.contDiffAt.of_le (by simp))] at h
  exact sub_eq_zero.mp h

/-- The normal-to-full jet implication is local to the signed chart. -/
theorem iteratedFDeriv_eqOn_of_pure_normal_jets_local [NeZero n] (hU : IsOpen U)
    {u v : X n → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hNormal : ∀ k, EqOn (chartDerivativeWord (List.replicate k i) u)
      (chartDerivativeWord (List.replicate k i) v) (boundaryFace U i)) :
    ∀ k, EqOn (iteratedFDeriv ℝ k u) (iteratedFDeriv ℝ k v) (boundaryFace U i) := by
  intro k p hp
  have hK : ({p} : Set (X n)) ⊆ U := singleton_subset_iff.mpr hp.1
  obtain ⟨u',hu',_,A,hA,hpA,hAU,huA⟩ :=
    CalderonN.exists_contDiff_extension_near_compact hU isCompact_singleton hK hu
  obtain ⟨v',hv',_,B,hB,hpB,hBU,hvB⟩ :=
    CalderonN.exists_contDiff_extension_near_compact hU isCompact_singleton hK hv
  have hAB : IsOpen (A ∩ B) := hA.inter hB
  have hpAB : p ∈ boundaryFace (A ∩ B) i :=
    ⟨⟨hpA (mem_singleton p),hpB (mem_singleton p)⟩,hp.2⟩
  have hJets (m : ℕ) : EqOn (chartDerivativeWord (List.replicate m i) u')
      (chartDerivativeWord (List.replicate m i) v') (boundaryFace (A ∩ B) i) := by
    intro x hx
    have h₁ := chartDerivativeWord_congr_germ (List.replicate m i)
      (Filter.mem_of_superset (hA.mem_nhds hx.1.1) huA)
    have h₂ := chartDerivativeWord_congr_germ (List.replicate m i)
      (Filter.mem_of_superset (hB.mem_nhds hx.1.2) hvB)
    exact h₁.eq_of_nhds.trans ((hNormal m ⟨hAU hx.1.1,hx.2⟩).trans h₂.eq_of_nhds.symm)
  have h₁ : u' =ᶠ[𝓝 p] u := Filter.mem_of_superset (hA.mem_nhds hpAB.1.1) huA
  have h₂ : v' =ᶠ[𝓝 p] v := Filter.mem_of_superset (hB.mem_nhds hpAB.1.2) hvB
  exact (h₁.iteratedFDeriv ℝ k).eq_of_nhds.symm.trans
    ((iteratedFDeriv_eqOn_of_pure_normal_jets hAB hu' hv' hJets k hpAB).trans
      (h₂.iteratedFDeriv ℝ k).eq_of_nhds)

/-- A scalar second-order equation determines all normal jets from the
first two. Each word on the right uses at most one normal derivative,
so zero value and normal derivative imply that the full jet vanishes. -/
theorem cauchy_normal_jets_eq_zero [NeZero n] (hU : IsOpen U) {u a : X n → ℝ}
    (hu : ContDiff ℝ ∞ u) (ha : ContDiff ℝ ∞ a)
    (ha₀ : ∀ x ∈ boundaryFace U i, a x ≠ 0)
    {ι : Type*} (s : Finset ι) (c : ι → X n → ℝ) (W : ι → List (I n))
    (hc : ∀ j ∈ s, ContDiff ℝ ∞ (c j)) (hW : ∀ j ∈ s, (W j).count i ≤ 1)
    (hEq : EqOn (a * chartDerivativeWord [i,i] u)
      (∑ j ∈ s, c j * chartDerivativeWord (W j) u) (U ∩ {x | 0 < x i}))
    (h0 : EqOn u 0 (boundaryFace U i)) (h1 : EqOn (coordDeriv i u) 0 (boundaryFace U i)) :
    ∀ x ∈ boundaryFace U i, ∀ k, iteratedFDeriv ℝ k u x = 0 := by
  classical
  let L (k : ℕ) := List.replicate k i
  let b (j : ι) : X n → ℝ := c j * chartDerivativeWord (W j) u
  have hb (j : ι) (hj : j ∈ s) : ContDiff ℝ ∞ (b j) := (hc j hj).mul (contDiff_chartDerivativeWord (W j) hu)
  have hB : ContDiff ℝ ∞ (∑ j ∈ s, b j) := by
    change ContDiff ℝ ∞ (fun x => (∑ j ∈ s, b j) x)
    simpa only [Finset.sum_apply] using ContDiff.sum (fun j hj => hb j hj)
  have hA : ContDiff ℝ ∞ (a * chartDerivativeWord [i,i] u) := ha.mul (contDiff_chartDerivativeWord _ hu)
  have hU' : IsOpen (U ∩ {x : X n | 0 < x i}) := hU.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous)
  have hEQ (k : ℕ) : EqOn (chartDerivativeWord (L k) (a * chartDerivativeWord [i,i] u))
      (chartDerivativeWord (L k) (∑ j ∈ s, b j)) (boundaryFace U i) := by
    have hclosed := isClosed_eq (contDiff_chartDerivativeWord (L k) hA).continuous
      (contDiff_chartDerivativeWord (L k) hB).continuous
    apply (boundaryFace_subset_closure_positive hU).trans
    apply closure_minimal (s := U ∩ {x : X n | 0 < x i}) _ hclosed
    intro x hx
    exact (chartDerivativeWord_congr_germ (L k) (Filter.mem_of_superset (hU'.mem_nhds hx) hEq)).eq_of_nhds
  have hNormal (m : ℕ) : EqOn (chartDerivativeWord (L m) u) 0 (boundaryFace U i) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      obtain rfl | rfl | ⟨k, rfl⟩ : m = 0 ∨ m = 1 ∨ ∃ k, m = k + 2 := by
        by_cases hm : m < 2
        · omega
        · exact Or.inr (Or.inr ⟨m - 2, by omega⟩)
      · exact h0
      · exact h1
      intro x hx
      have hvanish (V : List (I n)) (hV : V.count i < k + 2) : chartDerivativeWord V u x = 0 :=
        chartDerivativeWord_eqOn_zero_from_normal hU hu V (ih (V.count i) hV) hx
      have hLeft (V : List (I n)) (hV : V.length < k) :
          chartDerivativeWord V (chartDerivativeWord [i,i] u) x = 0 := by
        rw [← chartDerivativeWord_append]
        apply hvanish
        rw [List.count_append]
        have hCount : V.count i ≤ V.length := List.count_le_length
        simp only [List.count_cons_self, List.count_nil]
        omega
      have hRight (j : ι) (hj : j ∈ s) : chartDerivativeWord (L k) (b j) x = 0 := by
        have hZero (V : List (I n)) (hV : V.length ≤ k) :
            chartDerivativeWord V (chartDerivativeWord (W j) u) x = 0 := by
          rw [← chartDerivativeWord_append]
          apply hvanish
          rw [List.count_append]
          exact lt_of_le_of_lt (Nat.add_le_add (List.count_le_length.trans hV) (hW j hj)) (by omega)
        rw [show b j = c j * chartDerivativeWord (W j) u from rfl,
          chartDerivativeWord_mul_of_lower_zero (L k) (hc j hj) (contDiff_chartDerivativeWord _ hu)
            (fun V hV => hZero V (by simpa [L] using hV.le)), hZero (L k) (by simp [L]), mul_zero]
      have hh := hEQ k hx
      rw [chartDerivativeWord_mul_of_lower_zero (L k) ha (contDiff_chartDerivativeWord _ hu)
        (fun V hV => hLeft V (by simpa [L] using hV)), ← chartDerivativeWord_append,
        chartDerivativeWord_sum s (L k) b hb, Finset.sum_apply, Finset.sum_eq_zero hRight] at hh
      have hL : L k ++ [i,i] = L (k + 2) := by simp [L, List.replicate_add]
      rw [hL] at hh
      exact (mul_eq_zero.mp hh).resolve_left (ha₀ x hx)
  exact iteratedFDeriv_eq_zero_of_pure_normal_jets hU hu hNormal

end CalderonPatch
