module

public import Proof.CalderonN.Chart

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Ring
import Proof.CalderonN.ChartGeometry

@[expose] public section

noncomputable section
open Matrix Set
open scoped ContDiff

namespace CalderonPatch

open CalderonN (I X Mat MetricField coordDeriv christoffel hessian laplace)

/-- Symmetric matrices serve as the second-derivative component of a scalar jet. -/
def symmetricHessians (n : ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | A.transpose = A}
  zero_mem' := Matrix.transpose_zero
  add_mem' {A B} hA hB := by
    change A.transpose = A at hA
    change B.transpose = B at hB
    change (A + B).transpose = A + B
    rw [Matrix.transpose_add, hA, hB]
  smul_mem' c {A} hA := by
    change A.transpose = A at hA
    change (c • A).transpose = c • A
    rw [Matrix.transpose_smul, hA]

/-- Value, ordinary first partials and symmetric Hessian at one point. -/
abbrev ScalarSecondJet (n : ℕ) := ℝ × (I n → ℝ) × symmetricHessians n

variable {n : ℕ}

def secondJetGradient : ScalarSecondJet n →ₗ[ℝ] (I n → ℝ) where
  toFun v := v.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondJetHessian : ScalarSecondJet n →ₗ[ℝ] Mat n where
  toFun v := v.2.2.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Laplace–Beltrami operator as a linear functional on the second jet. -/
def laplaceOnSecondJet (γ : MetricField n) (x : X n) : ScalarSecondJet n →ₗ[ℝ] ℝ :=
  ∑ i : I n, ∑ j : I n, (γ x)⁻¹ i j •
    ((Matrix.entryLinearMap ℝ ℝ i j).comp secondJetHessian -
      ∑ k : I n, christoffel γ x k i j • (LinearMap.proj k).comp secondJetGradient)

theorem laplaceOnSecondJet_apply (γ : MetricField n) (x : X n) (v : ScalarSecondJet n) :
    laplaceOnSecondJet γ x v = ∑ i, ∑ j, (γ x)⁻¹ i j *
      (v.2.2.val i j - ∑ k, christoffel γ x k i j * v.2.1 k) := by
  simp only [laplaceOnSecondJet, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, smul_eq_mul]
  rfl

/-- The derivatives of a smooth function give its actual scalar jet. -/
def secondJet (u : X n → ℝ) (x : X n) (h : (hessian u x).transpose = hessian u x) :
    ScalarSecondJet n :=
  (u x, fun i => coordDeriv i u x, ⟨hessian u x, h⟩)

theorem laplaceOnSecondJet_secondJet (γ : MetricField n) (x : X n) (u : X n → ℝ)
    (h : (hessian u x).transpose = hessian u x) :
    laplaceOnSecondJet γ x (secondJet u x h) = laplace γ u x := by
  rw [laplaceOnSecondJet_apply]
  rfl

theorem laplaceOnSecondJet_zero_first (γ : MetricField n) (x : X n)
    (v : ℝ) (A : symmetricHessians n) :
    laplaceOnSecondJet γ x (v, 0, A) = ((γ x)⁻¹ * A.val).trace := by
  have hA (i j : I n) : A.val j i = A.val i j :=
    congrArg (fun H : Mat n => H i j) A.property
  rw [laplaceOnSecondJet_apply]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, Matrix.trace, Matrix.diag,
    Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    congrArg ((γ x)⁻¹ i j * ·) (hA i j).symm

/-- Any first derivative occurs in a harmonic second jet. An appropriate
multiple of the metric in the Hessian slot cancels the first-order term. -/
theorem exists_harmonicJet_with_first [NeZero n] (γ : MetricField n) (x : X n)
    (hg : (γ x).PosDef) (b : I n → ℝ) :
    ∃ v : ScalarSecondJet n, v.2.1 = b ∧ laplaceOnSecondJet γ x v = 0 := by
  let L := laplaceOnSecondJet γ x
  let v : ScalarSecondJet n := (0, b, 0)
  let m : ScalarSecondJet n := (0, 0, ⟨γ x, hg.isHermitian.isSymm.eq⟩)
  have hm : L m = n := by
    change laplaceOnSecondJet γ x (0, 0, ⟨γ x, hg.isHermitian.isSymm.eq⟩) = _
    rw [laplaceOnSecondJet_zero_first, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne'),
      Matrix.trace_one, Fintype.card_fin]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  refine ⟨v - ((L v) / (n : ℝ)) • m, ?_, ?_⟩
  · change b - ((L v) / (n : ℝ)) • (0 : I n → ℝ) = b
    simp
  · change L (v - ((L v) / (n : ℝ)) • m) = 0
    rw [map_sub, map_smul, hm, smul_eq_mul, div_mul_cancel₀ _ hn, sub_self]

/-- A linear span annihilated by the Laplacian is its full kernel if
every annihilating functional is a multiple of the Laplacian. -/
theorem span_eq_ker_of_annihilating_functionals {F V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] ℝ) (jet : F → V) (hH : ∀ a, L (jet a) = 0)
    (hAnn : ∀ A : Module.Dual ℝ V, (∀ a, A (jet a) = 0) → ∃ c : ℝ, A = c • L) :
    Submodule.span ℝ (range jet) = L.ker := by
  let S := Submodule.span ℝ (range jet)
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hH a)
  · intro x hx
    by_contra hout
    obtain ⟨A, hAx, hMap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hout inferInstance
    have hA : ∀ a, A (jet a) = 0 := by
      intro a
      have ha : A (jet a) ∈ S.map A :=
        Submodule.mem_map.mpr ⟨jet a, Submodule.subset_span (mem_range_self a), rfl⟩
      rwa [hMap, Submodule.mem_bot] at ha
    obtain ⟨c, rfl⟩ := hAnn A hA
    exact hAx (by change c * L x = 0; rw [LinearMap.mem_ker.mp hx, mul_zero])

/-- The annihilator calculation gives every harmonic jet as an actual
source jet when the source solution operator is linear. -/
theorem range_eq_ker_of_annihilating_functionals {F V : Type*}
    [AddCommGroup F] [Module ℝ F] [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] ℝ) (jet : F →ₗ[ℝ] V) (hH : ∀ a, L (jet a) = 0)
    (hAnn : ∀ A : Module.Dual ℝ V, (∀ a, A (jet a) = 0) → ∃ c : ℝ, A = c • L) :
    jet.range = L.ker := by
  simpa only [← LinearMap.coe_range, Submodule.span_eq] using
    span_eq_ker_of_annihilating_functionals L jet hH hAnn

end CalderonPatch
