module

public import Proof.Manuscript.GeometryClassicalRestriction

import Mathlib.Tactic

public section

noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace CalderonPaper

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If a chart symbol vanishes outside a closed output support, all its
mixed derivatives vanish there as well, throughout the open geometry set. -/
theorem angularMixedJet_zero_off_angularSupport
    {a : P × E → E → ℂ} {U : Set P} (hU : IsOpen U) {S : Set E} (hS : IsClosed S)
    {p : P} (hp : p ∈ U) {x : E} (hx : x ∉ S)
    (ha : ∀ q ∈ U, ∀ x ∉ S, ∀ ξ, a (q,x) ξ = 0) (ξ : E) (j l : ℕ) :
    angularMixedJet j l a (p,x) ξ = 0 := by
  have hNear : U ×ˢ Sᶜ ∈ 𝓝 (p,x) :=
    (hU.prod hS.isOpen_compl).mem_nhds ⟨hp,hx⟩
  have he : (fun q : P × E => iteratedFDeriv ℝ l (a q) ξ) =ᶠ[𝓝 (p,x)]
      (fun _ : P × E => 0) := by
    filter_upwards [hNear] with q hq
    have hVal : a q = 0 := funext (ha q.1 hq.1 q.2 hq.2)
    rw [hVal]
    change iteratedFDeriv ℝ l (fun _ : E => (0:ℂ)) ξ = 0
    simp only [iteratedFDeriv_fun_zero,Pi.zero_apply]
  unfold angularMixedJet
  simp only [(he.iteratedFDeriv ℝ j).eq_of_nhds,iteratedFDeriv_fun_zero,Pi.zero_apply]

theorem geometryClassicalSymbol_supported_bounds
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {dim : ℕ}
    {U J : Set P} (hU : IsOpen U) (hJU : J ⊆ U)
    {S : Set (AngularCoordinates dim)} (hS : IsClosed S)
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    {χ : AngularCoordinates dim → ℝ}
    {b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (m : ℤ)
    (ha₀ : ∀ q ∈ U, ∀ x ∉ S, ∀ ξ, a (q,x) ξ = 0)
    (hb₀ : ∀ j q, q ∈ U → ∀ x ∉ S, ∀ ξ, b j (q,x) ξ = 0)
    (hRest : ∀ N l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ∈ S, ∀ ξ,
      ‖angularMixedJet j l
        (fun q' ξ' => a q' ξ' - (χ ξ' : ℂ) * ∑ j' ∈ Finset.range N, b j' q' ξ') (q,x) ξ‖
      ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l)) :
    (∀ l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l a (q,x) ξ‖ ≤ C*(1+‖ξ‖)^((m:ℝ)-l)) ∧
    ∀ N l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l
        (fun q' ξ' => a q' ξ' - (χ ξ' : ℂ) * ∑ j' ∈ Finset.range N, b j' q' ξ') (q,x) ξ‖
      ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l) := by
  let R (N : ℕ) (q : P × AngularCoordinates dim) (ξ : AngularCoordinates dim) :=
    a q ξ - (χ ξ : ℂ) * ∑ j ∈ Finset.range N, b j q ξ
  have hRest' (N l j : ℕ) : ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l (R N) (q,x) ξ‖ ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l) := by
    obtain ⟨C,hC,hBd⟩ := hRest N l j
    refine ⟨C,hC,?_⟩
    intro q hq x ξ
    by_cases hx : x ∈ S
    · exact hBd q hq x hx ξ
    · have hOff (q' : P) (hq' : q' ∈ U) (x' : AngularCoordinates dim) (hx' : x' ∉ S)
          (ξ' : AngularCoordinates dim) : R N (q',x') ξ' = 0 := by
        simp [R,ha₀ q' hq' x' hx',hb₀ _ q' hq' x' hx']
      rw [angularMixedJet_zero_off_angularSupport hU hS (hJU hq) hx hOff ξ j l,norm_zero]
      positivity
  refine ⟨?_,hRest'⟩
  intro l j
  simpa only [R,Finset.range_zero,Finset.sum_empty,mul_zero,sub_zero,Int.cast_zero,Nat.cast_zero]
    using hRest' 0 l j

/-- A common closed support for a symbol and its homogeneous terms permits
well-founded bounds verified on the support to be used on the entire chart. -/
theorem geometryClassicalAngularSymbol_of_supported_remainders
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {dim : ℕ}
    {U J : Set P} (hU : IsOpen U) (hJU : J ⊆ U)
    {S : Set (AngularCoordinates dim)} (hS : IsClosed S)
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    {χ : AngularCoordinates dim → ℝ}
    {b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (m : ℤ)
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (hχ : ContDiff ℝ ∞ χ) (hχ₀ : ∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0)
    (hχ₁ : ∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 1)
    (hb : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (b j)) ((U ×ˢ univ) ×ˢ {0}ᶜ))
    (hHom : ∀ j q, q ∈ U → ∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
      b j (q,x) (r • ξ) = ((r^((m:ℝ)-j) : ℝ) : ℂ)*b j (q,x) ξ)
    (ha₀ : ∀ q ∈ U, ∀ x ∉ S, ∀ ξ, a (q,x) ξ = 0)
    (hb₀ : ∀ j q, q ∈ U → ∀ x ∉ S, ∀ ξ, b j (q,x) ξ = 0)
    (hRest : ∀ N l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ∈ S, ∀ ξ,
      ‖angularMixedJet j l
        (fun q' ξ' => a q' ξ' - (χ ξ' : ℂ) * ∑ j' ∈ Finset.range N, b j' q' ξ') (q,x) ξ‖
      ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l)) :
    UniformGeometryClassicalAngularSymbol U J m a := by
  obtain ⟨hA,hRest'⟩ := geometryClassicalSymbol_supported_bounds hU hJU hS m ha₀ hb₀ hRest
  exact ⟨ha,hA,χ,b,hχ,hχ₀,hχ₁,hb,hHom,hRest'⟩

end CalderonPaper
