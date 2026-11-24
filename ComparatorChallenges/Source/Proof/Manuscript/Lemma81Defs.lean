module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonPaper

/-- Smooth up to a prescribed closed set, by local smooth ambient extensions. -/
def SmoothThrough {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Set E) (f : E → V) : Prop :=
  ∀ p ∈ S, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
    ∃ f₀ : E → V, ContDiffOn ℝ ∞ f₀ U ∧ EqOn f₀ f (U ∩ S)

/-- A smooth boundary has local regular smooth defining functions, positive inside. -/
def HasSmoothEuclideanBoundary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) : Prop :=
  ∀ p ∈ frontier Ω, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
    ∃ ρ : E → ℝ, ContDiffOn ℝ ∞ ρ U ∧ ρ p = 0 ∧ fderiv ℝ ρ p ≠ 0 ∧
      ∀ x ∈ U, x ∈ Ω ↔ 0 < ρ x

/-- A self-diffeomorphism of the closure, smooth through the boundary and preserving the interior. -/
def IsClosureDiffeomorphism {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : Set E) (F : E → E) : Prop :=
  MapsTo F (closure Ω) (closure Ω) ∧ MapsTo F Ω Ω ∧ SmoothThrough (closure Ω) F ∧
    ∃ G : E → E, MapsTo G (closure Ω) (closure Ω) ∧ MapsTo G Ω Ω ∧
      SmoothThrough (closure Ω) G ∧ LeftInvOn G F (closure Ω) ∧ RightInvOn G F (closure Ω)

/-- The pullback of the Euclidean inner product by F is exp(2b) times the Euclidean inner product. -/
def EuclideanConformalOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (F : E → E) (b : E → ℝ) : Prop :=
  ∀ x ∈ Ω, ∀ v w : E,
    inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) =
      Real.exp (2 * b x) * inner ℝ v w

end CalderonPaper
