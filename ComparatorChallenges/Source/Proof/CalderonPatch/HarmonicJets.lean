module

public import Proof.CalderonN.Chart
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Proof.CalderonN.Coordinates

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

/-- The derivatives of a smooth function give its actual scalar jet. -/
def secondJet (u : X n → ℝ) (x : X n) (h : (hessian u x).transpose = hessian u x) :
    ScalarSecondJet n :=
  (u x, fun i => coordDeriv i u x, ⟨hessian u x, h⟩)

end CalderonPatch
