module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Adapted from `Calderon/CollaboratorUniqueContinuationDefinitionOct17.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

/-! # Weak unique continuation

Classical weak unique continuation for second-order elliptic equations in divergence form with
smooth symmetric positive definite coefficients (Aronszajn 1957; Hörmander's Carleman estimates;
e.g. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Thm 17.2.6):
a smooth solution of `div(A ∇u) = 0` on a connected open set that vanishes on a nonempty open
subset vanishes identically.

This module states the proposition and its divergence-form operator. The theorems that use it
take an explicit hypothesis `hUCP : UniqueContinuation`; the proposition is proved as
`uniqueContinuation` in `Proof.LocalMetricExtension.Elliptic.UniqueContinuation`. -/

noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace CalderonN.Carleman

variable {d : ℕ}

/-- The divergence-form operator `div(A ∇u)` at `x`, in coordinates. -/
def divCoeffGrad (A : (CalderonN.X d) → Matrix (Fin d) (Fin d) ℝ) (u : (CalderonN.X d) → ℝ) (x : (CalderonN.X d)) : ℝ :=
  ∑ i : Fin d, fderiv ℝ (fun z : (CalderonN.X d) => ∑ j : Fin d, A z i j *
    fderiv ℝ u z (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)

/-- **Weak unique continuation** for `div(A ∇u) = 0` with smooth, symmetric positive definite
`A` on a connected open set `Ω ⊆ ℝᵈ`. -/
def UniqueContinuation (d : ℕ) : Prop :=
  ∀ (Ω : Set (CalderonN.X d)), IsOpen Ω → IsConnected Ω →
    ∀ (A : (CalderonN.X d) → Matrix (Fin d) (Fin d) ℝ), ContDiffOn ℝ ∞ A Ω → (∀ x ∈ Ω, (A x).PosDef) →
    ∀ (u : (CalderonN.X d) → ℝ), ContDiffOn ℝ ∞ u Ω → (∀ x ∈ Ω, divCoeffGrad A u x = 0) →
    ∀ V : Set (CalderonN.X d), IsOpen V → V.Nonempty → V ⊆ Ω → (∀ x ∈ V, u x = 0) →
    ∀ x ∈ Ω, u x = 0


end CalderonN.Carleman
