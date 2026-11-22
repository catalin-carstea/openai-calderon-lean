module

public import Proof.CalderonPatch.DirichletMinimization

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

section Variational

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The Dirichlet energy with a linear source term. -/
def dirichletAction (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (ell : H →ₗ[ℝ] ℝ) (w : H) : ℝ :=
  B w w / 2 - ell w

/-- A weak solution of the Dirichlet equation minimizes the action,
with equality only at the solution when the form is positive definite. -/
theorem dirichletAction_minimizer (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (ell : H →ₗ[ℝ] ℝ)
    (hSym : ∀ u v, B u v = B v u) (hPos : ∀ v ≠ 0, 0 < B v v)
    {w : H} (hWeak : ∀ v, B w v = ell v) :
    ∀ v, dirichletAction B ell w ≤ dirichletAction B ell v ∧
      (dirichletAction B ell v = dirichletAction B ell w → v = w) := by
  intro v
  have hSquare : dirichletAction B ell v - dirichletAction B ell w = B (v - w) (v - w) / 2 := by
    have h1 := hWeak v
    have h2 := hWeak w
    have h3 := hSym v w
    simp only [dirichletAction, map_sub, LinearMap.sub_apply]
    linarith
  by_cases h : v = w
  · exact ⟨h ▸ le_rfl, fun _ => h⟩
  · have hStrict := hPos (v - w) (sub_ne_zero.mpr h)
    have hlt : dirichletAction B ell w < dirichletAction B ell v := by linarith
    exact ⟨hlt.le, fun he => False.elim (hlt.ne he.symm)⟩

end Variational

section CapAgreement

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M] [MeasurableSpace M]
  {H₁ H₂ V : Type*} [AddCommGroup H₁] [Module ℝ H₁] [AddCommGroup H₂] [Module ℝ H₂]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- A replacement in the opposite extension keeps the same cap
restriction and uses the original harmonic extension for the same trace.
The splitting equalities are for the actual Dirichlet actions on the
extended zero-trace spaces. -/
theorem cap_agreement_of_weakSolutions
    {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M} {Γ : Set ((𝓡∂ n).boundary M)}
    (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ)
    (B₁ : H₁ →ₗ[ℝ] H₁ →ₗ[ℝ] ℝ) (B₂ : H₂ →ₗ[ℝ] H₂ →ₗ[ℝ] ℝ)
    (ell₁ : H₁ →ₗ[ℝ] ℝ) (ell₂ : H₂ →ₗ[ℝ] ℝ)
    (hSym₁ : ∀ u v, B₁ u v = B₁ v u) (hSym₂ : ∀ u v, B₂ u v = B₂ v u)
    (hPos₁ : ∀ v ≠ 0, 0 < B₁ v v) (hPos₂ : ∀ v ≠ 0, 0 < B₂ v v)
    (cap₁ : H₁ → V) (cap₂ : H₂ → V) (capCost : V → ℝ)
    (w₁ : H₁) (w₂ : H₂) (hW₁ : ∀ z, B₁ w₁ z = ell₁ z) (hW₂ : ∀ z, B₂ w₂ z = ell₂ z)
    (f₁ f₂ : M → ℝ)
    (hf₁ : ContMDiff J R ∞ f₁) (hf₂ : ContMDiff J R ∞ f₂)
    (hs₁ : tsupport (fun p : (𝓡∂ n).boundary M => f₁ p) ⊆ Γ)
    (hs₂ : tsupport (fun p : (𝓡∂ n).boundary M => f₂ p) ⊆ Γ)
    (hSplit₁ : dirichletAction B₁ ell₁ w₁ =
      dirichletQuadraticEnergy g₁ μ₁ f₁ / 2 + capCost (cap₁ w₁))
    (hSplit₂ : dirichletAction B₂ ell₂ w₂ =
      dirichletQuadraticEnergy g₂ μ₂ f₂ / 2 + capCost (cap₂ w₂))
    (hReplace₂ : ∃ v₂, cap₂ v₂ = cap₁ w₁ ∧
      dirichletAction B₂ ell₂ v₂ = dirichletQuadraticEnergy g₂ μ₂ f₁ / 2 + capCost (cap₂ v₂))
    (hReplace₁ : ∃ v₁, cap₁ v₁ = cap₂ w₂ ∧
      dirichletAction B₁ ell₁ v₁ = dirichletQuadraticEnergy g₁ μ₁ f₂ / 2 + capCost (cap₁ v₁)) :
    cap₁ w₁ = cap₂ w₂ := by
  obtain ⟨v₂, hcap₂, hcost₂⟩ := hReplace₂
  obtain ⟨v₁, hcap₁, hcost₁⟩ := hReplace₁
  have hJ₂ : dirichletAction B₂ ell₂ v₂ = dirichletAction B₁ ell₁ w₁ := by
    rw [hcost₂, hSplit₁, hcap₂, hEnergy f₁ hf₁ hs₁]
  have hJ₁ : dirichletAction B₁ ell₁ v₁ = dirichletAction B₂ ell₂ w₂ := by
    rw [hcost₁, hSplit₂, hcap₁, hEnergy f₂ hf₂ hs₂]
  have hMin₁ := dirichletAction_minimizer B₁ ell₁ hSym₁ hPos₁ hW₁ v₁
  have hMin₂ := dirichletAction_minimizer B₂ ell₂ hSym₂ hPos₂ hW₂ v₂
  have hEq : dirichletAction B₂ ell₂ v₂ = dirichletAction B₂ ell₂ w₂ :=
    hMin₂.1.antisymm' (hJ₂.le.trans (hMin₁.1.trans hJ₁.le))
  exact hcap₂.symm.trans (congrArg cap₂ (hMin₂.2 hEq))

end CapAgreement

end CalderonPatch
