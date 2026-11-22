module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

public section

/-! Counted Cartesian grid adapted from `C3Spectral` and
`MixedKernelConstructionC3SupportV015` at anisotropic-calderon-lean revision
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace CalderonN

variable {dim : ℕ}

theorem ball_cell_geom (K0 : Set (X dim)) (d δ : ℝ) (hδd : δ ≤ d) (c : (X dim)) (hc : c ∈ K0) (x : (X dim))
    (hx : x ∈ ball c δ) :
    ‖x - c‖ ≤ δ ∧ ∀ t ∈ Icc (0 : ℝ) 1, c + t • (x - c) ∈ cthickening d K0 := by
  have hxc : ‖x - c‖ < δ := by rw [← dist_eq_norm]; exact hx
  refine ⟨hxc.le, fun t ht => ?_⟩
  refine mem_cthickening_of_dist_le _ c d K0 hc ?_
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc t * ‖x - c‖ ≤ 1 * δ := mul_le_mul ht.2 hxc.le (norm_nonneg _) zero_le_one
    _ ≤ d := by rw [one_mul]; exact hδd

/-- Two points in the same floor cell of mesh `1/a` are at distance `< 3/a`. -/
theorem floorCell_norm_lt (ρ a : ℝ) (ha : 0 < a) (x y : (X dim))
    (hx : ∀ j, 0 ≤ (x j + ρ) * a) (hy : ∀ j, 0 ≤ (y j + ρ) * a)
    (hxy : ∀ j, ⌊(x j + ρ) * a⌋₊ = ⌊(y j + ρ) * a⌋₊) : ‖x - y‖ < ((dim : ℝ) + 1) / a := by
  have hc : ∀ j, ((x j - y j) * a) ^ 2 < 1 := by
    intro j
    have h1 := Nat.lt_floor_add_one ((x j + ρ) * a)
    have h2 := Nat.lt_floor_add_one ((y j + ρ) * a)
    have h3 := Nat.floor_le (hx j)
    have h4 := Nat.floor_le (hy j)
    rw [hxy j] at h1 h3
    rw [sq_lt_one_iff_abs_lt_one, abs_lt]
    constructor <;> nlinarith
  have hsq : ‖x - y‖ ^ 2 * a ^ 2 ≤ (dim : ℝ) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Finset.sum_mul]
    calc
      _ = ∑ j : Fin dim, ((x j - y j) * a) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, mul_pow]
      _ ≤ ∑ _ : Fin dim, (1 : ℝ) := Finset.sum_le_sum fun j _ => (hc j).le
      _ = _ := by simp
  have hscale : (((dim : ℝ) + 1) / a) ^ 2 * a ^ 2 = ((dim : ℝ) + 1) ^ 2 := by
    rw [div_pow, div_mul_cancel₀]
    positivity
  have hlt : ‖x - y‖ ^ 2 < (((dim : ℝ) + 1) / a) ^ 2 := by
    by_contra h
    push Not at h
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg a)
    rw [hscale] at hmul
    nlinarith [Nat.cast_nonneg (α := ℝ) dim, sq_nonneg (dim : ℝ)]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

/-- The Cartesian floor grid of mesh `1/a` on the coordinate cube, cut down to `S`,
with empty cells excluded (so no case split on `S = ∅`). Centres are actual points of `S`. -/
theorem exists_floor_grid (S K0 : Set (X dim)) (hS : MeasurableSet S) (hSK0 : S ⊆ K0) (r : ℕ)
    (hr : ∀ x ∈ K0, ∀ j, |x j| < (r : ℝ)) (a : ℕ) (hapos : (0 : ℝ) < a) :
    ∃ (N : ℕ) (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)),
      (∀ i, MeasurableSet (Q i)) ∧ Pairwise (fun i j => Disjoint (Q i) (Q j)) ∧
      S ⊆ ⋃ i, Q i ∧ (∀ i, c i ∈ S) ∧ (∀ i, ∀ x ∈ Q i, ‖x - c i‖ < ((dim : ℝ) + 1) / (a : ℝ)) ∧
      N ≤ (2 * r * a) ^ dim := by
  classical
  let fl : (X dim) → Fin dim → ℕ := fun x j => ⌊(x j + (r : ℝ)) * (a : ℝ)⌋₊
  let n : ℕ := 2 * r * a
  let Qz : (Fin dim → ℕ) → Set (X dim) := fun z => S ∩ {x | fl x = z}
  let T : Finset (Fin dim → ℕ) :=
    (Fintype.piFinset fun _ : Fin dim => Finset.range n).filter fun z => (Qz z).Nonempty
  let e : Fin T.card ≃ T := T.equivFin.symm
  have hne : ∀ i, (Qz (e i : Fin dim → ℕ)).Nonempty := fun i => (Finset.mem_filter.mp (e i).2).2
  let Q : Fin T.card → Set (X dim) := fun i => Qz (e i : Fin dim → ℕ)
  let c : Fin T.card → (X dim) := fun i => (hne i).some
  have hpos_coord : ∀ x ∈ K0, ∀ j, 0 ≤ (x j + (r : ℝ)) * (a : ℝ) := by
    intro x hx j
    have h1 := hr x hx j
    rw [abs_lt] at h1
    exact mul_nonneg (by linarith) hapos.le
  have hcQ : ∀ i, c i ∈ Q i := fun i => (hne i).some_mem
  refine ⟨T.card, Q, c, ?_, ?_, ?_, fun i => (hcQ i).1, ?_, ?_⟩
  · intro i
    refine hS.inter ?_
    have hflm : ∀ j : Fin dim, Measurable fun x : (X dim) => ⌊(x j + (r : ℝ)) * (a : ℝ)⌋₊ := fun j =>
      ((((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable).add_const _).mul_const
        _).nat_floor
    have hset : {x : (X dim) | fl x = (e i : Fin dim → ℕ)} =
        ⋂ j, (fun x : (X dim) => ⌊(x j + (r : ℝ)) * (a : ℝ)⌋₊) ⁻¹' {(e i : Fin dim → ℕ) j} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_singleton_iff, fl, funext_iff]
    show MeasurableSet {x : (X dim) | fl x = (e i : Fin dim → ℕ)}
    rw [hset]
    exact MeasurableSet.iInter fun j => hflm j (measurableSet_singleton _)
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    have h1 : fl x = (e i : Fin dim → ℕ) := hxi.2
    have h2 : fl x = (e j : Fin dim → ℕ) := hxj.2
    exact e.injective (Subtype.ext (h1.symm.trans h2))
  · intro x hxS
    have hxK := hSK0 hxS
    have hzT : fl x ∈ T := by
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, ⟨x, hxS, rfl⟩⟩
      refine Finset.mem_range.mpr ((Nat.floor_lt (hpos_coord x hxK j)).mpr ?_)
      have h1 := hr x hxK j
      rw [abs_lt] at h1
      have h2 : (x j + (r : ℝ)) * (a : ℝ) < (2 * r : ℝ) * a :=
        mul_lt_mul_of_pos_right (by linarith) hapos
      have h3 : ((n : ℕ) : ℝ) = (2 * r : ℝ) * a := by simp only [n]; push_cast; ring
      rw [h3]
      exact h2
    refine mem_iUnion.mpr ⟨e.symm ⟨fl x, hzT⟩, ?_⟩
    show x ∈ Qz (e (e.symm ⟨fl x, hzT⟩) : Fin dim → ℕ)
    rw [Equiv.apply_symm_apply]
    exact ⟨hxS, rfl⟩
  · intro i x hx
    have h1 : fl x = (e i : Fin dim → ℕ) := hx.2
    have h2 : fl (c i) = (e i : Fin dim → ℕ) := (hcQ i).2
    exact floorCell_norm_lt (r : ℝ) (a : ℝ) hapos x (c i) (hpos_coord x (hSK0 hx.1))
      (hpos_coord (c i) (hSK0 (hcQ i).1)) (fun j => congrFun (h1.trans h2.symm) j)
  · calc T.card ≤ (Fintype.piFinset fun _ : Fin dim => Finset.range n).card :=
          Finset.card_filter_le _ _
      _ = n ^ dim := by
          rw [Fintype.card_piFinset]
          simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- C3-D4 arithmetic: resolutions above `⌈3/d⌉₊ + 1` have mesh `3/a ≤ d`. -/
theorem resolution_room (d : ℝ) (hd : 0 < d) (a : ℕ) (ha : ⌈((dim : ℝ) + 1) / d⌉₊ + 1 ≤ a) :
    (1 : ℝ) ≤ a ∧ ((dim : ℝ) + 1) / (a : ℝ) ≤ d := by
  have h2 : (⌈((dim : ℝ) + 1) / d⌉₊ : ℝ) + 1 ≤ a := by exact_mod_cast ha
  have h1 : ((dim : ℝ) + 1) / d ≤ (⌈((dim : ℝ) + 1) / d⌉₊ : ℝ) := Nat.le_ceil _
  have h0 : (0 : ℝ) ≤ (⌈((dim : ℝ) + 1) / d⌉₊ : ℝ) := Nat.cast_nonneg _
  have ha1 : (1 : ℝ) ≤ a := by linarith
  refine ⟨ha1, ?_⟩
  have hapos : (0 : ℝ) < a := by linarith
  have h3 : ((dim : ℝ) + 1) / d < a := by linarith
  rw [div_lt_iff₀ hd] at h3
  rw [div_le_iff₀ hapos]
  linarith

/-- C3-D4 arithmetic: the ambient-dimensional rank count. -/
theorem counted_rank_le (N' r a σ : ℕ) (hT : N' ≤ (2 * r * a) ^ dim) (x : ℕ) (hx : x ≤ N' * σ) :
    x ≤ 2 ^ dim * r ^ dim * σ * a ^ dim := by
  have h1 : N' * σ ≤ (2 * r * a) ^ dim * σ := Nat.mul_le_mul_right σ hT
  have h2 : (2 * r * a) ^ dim * σ = 2 ^ dim * r ^ dim * σ * a ^ dim := by
    simp only [mul_pow]
    ring
  exact hx.trans (h1.trans h2.le)

/-- C3-D4 arithmetic: the error rate `L(3/a)^(s+1)·a^s ≤ L·3^(s+1)` for `a ≥ 1`. -/
theorem counted_error_le (L : ℝ) (hL : 0 ≤ L) (a : ℕ) (ha1 : (1 : ℝ) ≤ a) (s : ℕ) (E : ℝ)
    (_hE0 : 0 ≤ E) (hE : E ≤ L * (((dim : ℝ) + 1) / (a : ℝ)) ^ (s + 1)) :
    E * (a : ℝ) ^ s ≤ L * ((dim : ℝ) + 1) ^ (s + 1) := by
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha1
  have hid : (((dim : ℝ) + 1) / (a : ℝ)) ^ (s + 1) * (a : ℝ) ^ s = ((dim : ℝ) + 1) ^ (s + 1) / a := by
    rw [div_pow, pow_succ (a : ℝ) s, div_mul_eq_mul_div,
      div_eq_div_iff (mul_pos (pow_pos hapos s) hapos).ne' hapos.ne']
    ring
  have hpow : (0 : ℝ) ≤ (a : ℝ) ^ s := pow_nonneg hapos.le s
  calc E * (a : ℝ) ^ s ≤ L * (((dim : ℝ) + 1) / (a : ℝ)) ^ (s + 1) * (a : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hE hpow
    _ = L * (((dim : ℝ) + 1) ^ (s + 1) / a) := by rw [mul_assoc, hid]
    _ ≤ L * ((dim : ℝ) + 1) ^ (s + 1) :=
        mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg (by positivity) _) ha1) hL

/-- The counted-grid construction factored through an arbitrary continuous linear map.
The concrete native Taylor theorem supplies `hP`; this is not a new endpoint premise. -/
theorem counted_approx_of_cell_taylor_family {ι : Type*} {E : ι → Type*} {F : Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ∀ p, E p →L[ℝ] F) (S K0 : Set (X dim)) (hS : MeasurableSet S)
    (hSK0 : S ⊆ K0) (hK0 : IsCompact K0) (d : ℝ) (hd : 0 < d) (s : ℕ)
    (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ (p : ι) (N : ℕ) (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (δ : ℝ), 0 ≤ δ →
      (∀ i, MeasurableSet (Q i)) → Pairwise (fun i j => Disjoint (Q i) (Q j)) →
      S ⊆ ⋃ i, Q i → (∀ i, c i ∈ cthickening d K0) →
      (∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ ∧
        ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ cthickening d K0) →
      ∃ P : E p →L[ℝ] F,
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤
          N * ∑ k ∈ Finset.range (s + 1), dim ^ k ∧
        ‖R p - P‖ ≤ L * δ ^ (s + 1)) :
    ∃ (B : ℝ) (N A0 : ℕ), ∀ (p : ι) (a : ℕ), A0 ≤ a →
      ∃ P : E p →L[ℝ] F,
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ N * a ^ dim ∧
        ‖R p - P‖ * (a : ℝ) ^ s ≤ B := by
  classical
  obtain ⟨ρ0, hρ0⟩ := hK0.isBounded.subset_closedBall (0 : (X dim))
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, (r : ℝ) = (⌈ρ0⌉₊ : ℝ) + 1 := ⟨⌈ρ0⌉₊ + 1, by push_cast; rfl⟩
  have hr : ∀ x ∈ K0, ∀ j, |x j| < (r : ℝ) := by
    intro x hx j
    have h1 : ‖x j‖ ≤ ‖x‖ := PiLp.norm_apply_le x j
    have h2 : ‖x‖ ≤ ρ0 := mem_closedBall_zero_iff.mp (hρ0 hx)
    have h3 : ρ0 ≤ ⌈ρ0⌉₊ := Nat.le_ceil ρ0
    rw [Real.norm_eq_abs] at h1
    rw [hrdef]
    linarith
  refine ⟨L * ((dim : ℝ) + 1) ^ (s + 1), 2 ^ dim * r ^ dim * ∑ k ∈ Finset.range (s + 1), dim ^ k, ⌈((dim : ℝ) + 1) / d⌉₊ + 1, ?_⟩
  intro p a ha
  obtain ⟨ha1, h3d⟩ := resolution_room (dim := dim) d hd a ha
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha1
  obtain ⟨N', Q, c, hQ, hdisj, hcover, hcS, hlt, hT⟩ :=
    exists_floor_grid S K0 hS hSK0 r hr a hapos
  have hgeom : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ ((dim : ℝ) + 1) / (a : ℝ) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ cthickening d K0 := fun i x hx =>
    ball_cell_geom K0 d (((dim : ℝ) + 1) / (a : ℝ)) h3d (c i) (hSK0 (hcS i)) x
      (by rw [mem_ball, dist_eq_norm]; exact hlt i x hx)
  obtain ⟨P, hPfin, hPrank, hPerr⟩ := hP p N' Q c (((dim : ℝ) + 1) / (a : ℝ)) (div_nonneg (by positivity) hapos.le)
    hQ hdisj hcover (fun i => self_subset_cthickening K0 (hSK0 (hcS i))) hgeom
  exact ⟨P, hPfin, counted_rank_le (dim := dim) N' r a _ hT _ hPrank,
    counted_error_le (dim := dim) L hL a ha1 s _ (norm_nonneg _) hPerr⟩

theorem counted_approx_of_cell_taylor {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : E →L[ℝ] F) (S K0 : Set (X dim)) (hS : MeasurableSet S)
    (hSK0 : S ⊆ K0) (hK0 : IsCompact K0) (d : ℝ) (hd : 0 < d) (s : ℕ)
    (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ (N : ℕ) (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (δ : ℝ), 0 ≤ δ →
      (∀ i, MeasurableSet (Q i)) → Pairwise (fun i j => Disjoint (Q i) (Q j)) →
      S ⊆ ⋃ i, Q i → (∀ i, c i ∈ cthickening d K0) →
      (∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ ∧
        ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ cthickening d K0) →
      ∃ P : E →L[ℝ] F,
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤
          N * ∑ k ∈ Finset.range (s + 1), dim ^ k ∧
        ‖R - P‖ ≤ L * δ ^ (s + 1)) :
    ∃ (B : ℝ) (N A0 : ℕ), ∀ a : ℕ, A0 ≤ a →
      ∃ P : E →L[ℝ] F,
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ N * a ^ dim ∧
        ‖R - P‖ * (a : ℝ) ^ s ≤ B := by
  obtain ⟨B,N,A,h⟩ := counted_approx_of_cell_taylor_family
    (ι := Unit) (E := fun _ => E) (fun _ => R) S K0 hS hSK0 hK0 d hd s L hL (fun _ => hP)
  exact ⟨B,N,A,h ()⟩


end CalderonN
