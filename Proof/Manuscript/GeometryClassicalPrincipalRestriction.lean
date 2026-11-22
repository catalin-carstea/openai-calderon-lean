module

public import Proof.Manuscript.GeometryClassicalRestriction

import Mathlib.Tactic

public section

noncomputable section
open CalderonN MeasureTheory Set
open scoped ContDiff

namespace CalderonPaper

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {dim : ℕ}

/-- The given classical expansion has zero principal coefficient on the
geometry points reached by a physical profile. -/
@[expose] def GeometryClassicalSymbolPrincipalZero (U J Z : Set P) (order : ℤ)
    (a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ) ∧
  (∀ l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
    ‖angularMixedJet j l a (q,x) ξ‖ ≤ C*(1+‖ξ‖)^((order:ℝ)-l)) ∧
  ∃ (χ : AngularCoordinates dim → ℝ)
    (b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ),
    ContDiff ℝ ∞ χ ∧ (∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0) ∧ (∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 1) ∧
    (∀ j, ContDiffOn ℝ ∞ (Function.uncurry (b j)) ((U ×ˢ univ) ×ˢ {0}ᶜ)) ∧
    (∀ j q, q ∈ U → ∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
      b j (q,x) (r • ξ) = ((r^((order:ℝ)-j) : ℝ) : ℂ)*b j (q,x) ξ) ∧
    (∀ N l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l
        (fun q' ξ' => a q' ξ' - (χ ξ' : ℂ) * ∑ j' ∈ Finset.range N, b j' q' ξ') (q,x) ξ‖
      ≤ C*(1+‖ξ‖)^((order-(N:ℤ):ℝ)-l)) ∧
    ∀ q ∈ Z, ∀ x ξ, ξ ≠ 0 → b 0 (q,x) ξ = 0

/-- Quantization of an operator with a principal coefficient that vanishes
on the selected restriction, together with its own smooth off-diagonal kernels. -/
@[expose] def GeometryClassicalSphereOperatorPrincipalZero (U J Z : Set P) (order : ℤ)
    [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] (A : P → SphereOperator dim) : Prop :=
  (∀ v : ↥(standardSphere dim),
    let κ := stereographic' (dim - 1) v
    ∀ χ η : X dim → ℂ, smoothNear χ (standardSphere dim) → smoothNear η (standardSphere dim) →
      angularSupport χ ⊆ κ.source → angularSupport η ⊆ κ.source →
      ∃ a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ,
        GeometryClassicalSymbolPrincipalZero U J Z order a ∧
        ∀ q ∈ J, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
          ∀ x ∈ κ.target,
            let localizedDatum := fun z : AngularCoordinates dim => η (κ.symm z) * u (κ.symm z)
            let integrand := fun ξ : AngularCoordinates dim =>
              angularFourierPhase x ξ * a (q,x) ξ * angularFourierTransform localizedDatum ξ
            Integrable localizedDatum ∧ Integrable integrand ∧
              χ (κ.symm x) * A q (fun w => η w * u w) (κ.symm x) = ∫ ξ, integrand ξ) ∧
  ∀ χ η : X dim → ℂ, smoothNear χ (standardSphere dim) → smoothNear η (standardSphere dim) →
    Disjoint (angularSupport χ) (angularSupport η) →
    ∃ K : P × X dim → X dim → ℂ, UniformGeometryAngularSmoothing U J K ∧
      ∀ q ∈ J, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
        ∀ w : ↥(standardSphere dim),
          χ w * A q (fun z => η z * u z) w =
            ∫ z : ↥(standardSphere dim), K (q,w) z * u z ∂(sphereProbability dim)

theorem GeometryClassicalSphereOperatorPrincipalZero.pullback
    [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]
    {T : Type} {Y : Set (X dim)} (hY : IsOpen Y) {U J Z : Set P}
    (hU : IsOpen U) (hJU : J ⊆ U) {m : ℤ} {A : P → SphereOperator dim}
    (hA : GeometryClassicalSphereOperatorPrincipalZero U J Z m A)
    {p : T → X dim → P} {β : T → X dim → ℝ}
    (hp : ∀ t, ContDiff ℝ ∞ (p t)) (hJ : ∀ t, MapsTo (p t) Y J)
    (hZ : ∀ t, MapsTo (p t) Y Z) (hβ : ∀ t y, y ∈ Y → 1 ≤ β t y)
    {D : ℝ} (hD : 1 ≤ D)
    (hP : ∀ t y, y ∈ Y → ∀ n ≤ 6, ‖iteratedFDeriv ℝ n (p t) y‖ ≤ D*(β t y)^n) :
    UniformClassicalSphereOperator Y β (m-1) (fun t y => A (p t y)) := by
  refine ⟨?_,?_⟩
  · intro v κ χ η hχ hη hχκ hηκ
    obtain ⟨a,ha,hEq⟩ := hA.1 v χ η hχ hη hχκ hηκ
    obtain ⟨hsm,hA,ζ,b,hζ,hζ₀,hζ₁,hb,hHom,hRest,hZero⟩ := ha
    refine ⟨fun t y x ξ => a (p t y,x) ξ,?_,fun t y hy => hEq (p t y) (hJ t hy)⟩
    exact geometryClassicalSymbol_lower_order_of_principal_zero_pullback hY hU hJU
      hsm hA hζ hζ₀ hζ₁ hb hHom hRest hp hJ hβ hD hP
      (fun t y hy => hZero (p t y) (hZ t hy))
  · intro χ η hχ hη hDisjoint
    obtain ⟨K,hK,hEq⟩ := hA.2 χ η hχ hη hDisjoint
    exact ⟨fun t y w z => K (p t y,w) z,hK.pullback hJU hp hJ hβ hD hP,
      fun t y hy => hEq (p t y) (hJ t hy)⟩

end CalderonPaper
