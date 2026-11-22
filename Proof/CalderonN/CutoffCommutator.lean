module

public import Proof.CalderonN.EllipticCalculus

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic

@[expose] public section

/-! The cutoff commutator and Caccioppoli inequality are adopted from
`MixedKernelConstructionC4SupportV015` at anisotropic-calderon-lean revision
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace CalderonN.Elliptic.CutoffCommutator

variable {dim : ℕ}

/-- P1: second product rule for native partials. -/
theorem pd_pd_mul {f g : (X dim) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i j : Fin dim) (x : (X dim)) :
    pd i (pd j (fun y => f y * g y)) x =
      pd i (pd j f) x * g x + pd j f x * pd i g x +
        pd i f x * pd j g x + f x * pd i (pd j g) x := by
  have hfirst : pd j (fun y => f y * g y) =
      fun y => pd j f y * g y + f y * pd j g y :=
    funext fun y => pd_mul hf hg y
  rw [hfirst, pd_add ((contDiff_pd hf).mul hg) (hf.mul (contDiff_pd hg)),
    pd_mul (contDiff_pd hf) hg, pd_mul hf (contDiff_pd hg)]
  ring

/-- P2: expansion of the literal divergence operator. -/
theorem Lop_expand (a : Fin dim → Fin dim → (X dim) → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) {u : (X dim) → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : (X dim)) :
    Lop a u x = ∑ i, ∑ j,
      (pd i (a i j) x * pd j u x + a i j x * pd i (pd j u) x) := by
  unfold Lop
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_sum (fun j => (ha i j).mul (contDiff_pd hu))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact pd_mul (ha i j) (contDiff_pd hu) x

/-- P3: the symmetric-coefficient cutoff commutator. -/
theorem Lop_mul_symm (a : Fin dim → Fin dim → (X dim) → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hs : ∀ i j x, a i j x = a j i x)
    {chi u : (X dim) → ℝ} (hc : ContDiff ℝ ∞ chi) (hu : ContDiff ℝ ∞ u) (x : (X dim)) :
    Lop a (fun y => chi y * u y) x =
      chi x * Lop a u x + u x * Lop a chi x +
        2 * ∑ i, ∑ j, a i j x * pd i chi x * pd j u x := by
  have hswap : (∑ i, ∑ j, a i j x * pd j chi x * pd i u x) =
      ∑ i, ∑ j, a i j x * pd i chi x * pd j u x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hs j i]
  rw [Lop_expand a ha (hc.mul hu), Lop_expand a ha hu, Lop_expand a ha hc, ← hswap]
  rw [show (2 * ∑ i, ∑ j, a i j x * pd j chi x * pd i u x) =
      (∑ i, ∑ j, a i j x * pd j chi x * pd i u x) + (∑ i, ∑ j, a i j x * pd i chi x * pd j u x)
      from by rw [hswap, two_mul]]
  simp only [pd_mul hc hu, pd_pd_mul hc hu, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- P4 (COMM): a scalar `b` OUTSIDE the divergence; no derivative of `b` appears. -/
theorem beta_Lop_cutoff_comm (a : Fin dim → Fin dim → (X dim) → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hs : ∀ i j x, a i j x = a j i x)
    {chi u : (X dim) → ℝ} (hc : ContDiff ℝ ∞ chi) (hu : ContDiff ℝ ∞ u)
    (b : (X dim) → ℝ) (x : (X dim)) :
    b x * Lop a (fun y => chi y * u y) x - chi x * (b x * Lop a u x) =
      b x * (u x * Lop a chi x +
        2 * ∑ i, ∑ j, a i j x * pd i chi x * pd j u x) := by
  rw [Lop_mul_symm a ha hs hc hu]
  ring

/-- L2: the literal divergence operator depends only on the germ. -/
theorem Lop_congr_of_eventuallyEq (a : Fin dim → Fin dim → (X dim) → ℝ) {f g : (X dim) → ℝ} {x : (X dim)}
    (h : f =ᶠ[nhds x] g) : Lop a f x = Lop a g x := by
  unfold Lop
  refine Finset.sum_congr rfl fun i _ => pd_congr_of_eventuallyEq ?_ i
  have hk : ∀ k, ∀ᶠ y in nhds x, pd k f y = pd k g y := fun k =>
    h.eventuallyEq_nhds.mono fun y hy => pd_congr_of_eventuallyEq hy k
  filter_upwards [Filter.eventually_all.2 hk] with y hy
  simp only [hy]


/-- Off the cutoff support the product has zero germ. -/
theorem mul_eventuallyEq_zero_of_not_mem_tsupport {chi : (X dim) → ℝ} (w : (X dim) → ℝ) {x : (X dim)}
    (hx : x ∉ tsupport chi) : (fun y => chi y * w y) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
  Filter.mem_of_superset ((isClosed_tsupport chi).isOpen_compl.mem_nhds hx) fun y hy => by
    have h0 : chi y = 0 := by
      by_contra h
      exact hy (subset_tsupport chi h)
    show chi y * w y = 0
    rw [h0, zero_mul]

/-- Z1: the literal divergence operator kills constants. -/
theorem Lop_const_zero (a : Fin dim → Fin dim → (X dim) → ℝ) (x : (X dim)) :
    Lop a (fun _ => (0 : ℝ)) x = 0 := by
  simp [Lop, pd, coordDeriv]

/-- Z1: off `tsupport chi`, `Lop a (chi*w)`, `Lop a chi` and every `pd i chi` vanish. -/
theorem Lop_mul_eq_zero_of_not_mem_tsupport (a : Fin dim → Fin dim → (X dim) → ℝ) {chi : (X dim) → ℝ}
    (w : (X dim) → ℝ) {x : (X dim)} (hx : x ∉ tsupport chi) :
    Lop a (fun y => chi y * w y) x = 0 := by
  rw [Lop_congr_of_eventuallyEq a (mul_eventuallyEq_zero_of_not_mem_tsupport w hx)]
  exact Lop_const_zero a x

theorem chi_eventuallyEq_zero_of_not_mem_tsupport {chi : (X dim) → ℝ} {x : (X dim)}
    (hx : x ∉ tsupport chi) : chi =ᶠ[nhds x] fun _ => (0 : ℝ) := by
  have h := mul_eventuallyEq_zero_of_not_mem_tsupport (chi := chi) (fun _ => (1 : ℝ)) hx
  simpa using h

theorem Lop_eq_zero_of_not_mem_tsupport (a : Fin dim → Fin dim → (X dim) → ℝ) {chi : (X dim) → ℝ}
    {x : (X dim)} (hx : x ∉ tsupport chi) : Lop a chi x = 0 := by
  rw [Lop_congr_of_eventuallyEq a (chi_eventuallyEq_zero_of_not_mem_tsupport hx)]
  exact Lop_const_zero a x

theorem pd_eq_zero_of_not_mem_tsupport {chi : (X dim) → ℝ} {x : (X dim)} (hx : x ∉ tsupport chi)
    (i : Fin dim) : pd i chi x = 0 := by
  rw [pd_congr_of_eventuallyEq (chi_eventuallyEq_zero_of_not_mem_tsupport hx) i]
  simp [pd, coordDeriv]

/-- Z3: where the cutoff is locally constant its partials vanish. -/
theorem pd_eq_zero_of_eventuallyEq_const {chi : (X dim) → ℝ} {x : (X dim)} {c : ℝ}
    (h : chi =ᶠ[nhds x] fun _ => c) (i : Fin dim) : pd i chi x = 0 := by
  rw [pd_congr_of_eventuallyEq h i]
  simp [pd, coordDeriv]

/-- Z3: where the cutoff is locally constant, `Lop a chi` vanishes. -/
theorem Lop_eq_zero_of_eventuallyEq_const (a : Fin dim → Fin dim → (X dim) → ℝ) {chi : (X dim) → ℝ}
    {x : (X dim)} {c : ℝ} (h : chi =ᶠ[nhds x] fun _ => c) : Lop a chi x = 0 := by
  rw [Lop_congr_of_eventuallyEq a h]
  simp [Lop, pd, coordDeriv]


end CalderonN.Elliptic.CutoffCommutator
