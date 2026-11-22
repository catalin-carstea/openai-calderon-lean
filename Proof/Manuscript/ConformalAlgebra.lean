module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic

public section

open scoped BigOperators

namespace CalderonPaper

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def conformalConnection (b : ι → ℝ) (i j k : ι) : ℝ :=
  (if k = j then b i else 0) + (if k = i then b j else 0) - (if i = j then b k else 0)

@[expose] def conformalCurvature (b : ι → ℝ) (S : ι → ι → ℝ) (i j k a : ι) : ℝ :=
  conformalConnection (S i) j k a - conformalConnection (S j) i k a +
    (∑ l, conformalConnection b j k l * conformalConnection b i l a) -
    (∑ l, conformalConnection b i k l * conformalConnection b j l a)

private theorem conformalCurvature_sectional (b : ι → ℝ) (S : ι → ι → ℝ)
    {i j : ι} (hij : i ≠ j) :
    conformalCurvature b S i j j i =
      -(S i i - b i ^ 2) - (S j j - b j ^ 2) - ∑ l, b l ^ 2 := by
  simp [conformalCurvature, conformalConnection, hij, Ne.symm hij,
    add_mul, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ite_mul, mul_ite, eq_comm (a := i), eq_comm (a := j), pow_two]
  ring

private theorem conformalCurvature_offDiagonal (b : ι → ℝ) (S : ι → ι → ℝ)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    conformalCurvature b S i j k i = -(S j k - b j * b k) := by
  simp [conformalCurvature, conformalConnection, hij, Ne.symm hij, hik, hjk, add_mul,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
    eq_comm (a := i), eq_comm (a := j)]
  ring

private theorem exists_index_ne_pair (hι : 3 ≤ Fintype.card ι) {i j : ι} (hij : i ≠ j) :
    ∃ k : ι, k ≠ i ∧ k ≠ j := by
  let rest := ((Finset.univ : Finset ι).erase i).erase j
  have hrest : 0 < rest.card := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hij]), Finset.card_erase_of_mem (by simp)]
    simp only [Finset.card_univ]
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hrest
  simp only [rest, Finset.mem_erase, Finset.mem_univ, and_true] at hk
  exact ⟨k, hk.2, hk.1⟩

/-- Vanishing curvature for the connection of a conformal Euclidean metric
determines every Hessian entry of the logarithmic scale. -/
theorem conformalHessian_eq_of_flat (hι : 3 ≤ Fintype.card ι) (b : ι → ℝ) (S : ι → ι → ℝ)
    (hflat : ∀ i j k a, conformalCurvature b S i j k a = 0) (i j : ι) :
    S i j = b i * b j - if i = j then (∑ k, b k ^ 2) / 2 else 0 := by
  by_cases hij : i = j
  · subst j
    have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨j, hj⟩ := exists_ne i
    obtain ⟨k, hki, hkj⟩ := exists_index_ne_pair hι hj.symm
    have eq₁ := (conformalCurvature_sectional b S hj.symm).symm.trans (hflat i j j i)
    have eq₂ := (conformalCurvature_sectional b S hki.symm).symm.trans (hflat i k k i)
    have eq₃ := (conformalCurvature_sectional b S hkj.symm).symm.trans (hflat j k k j)
    simp [← pow_two]
    linarith
  · obtain ⟨k, hki, hkj⟩ := exists_index_ne_pair hι hij
    have eq := (conformalCurvature_offDiagonal b S hki hkj hij).symm.trans (hflat k i j k)
    simp [hij]
    linarith

end CalderonPaper
