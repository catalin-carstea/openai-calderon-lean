module

public import Proof.CalderonPatch.BoundaryJetAlgebra

import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Matrix Set

namespace CalderonPatch

open CalderonN (X Mat metricPair metricPair_nonneg_of_posDef)

variable {m : ℕ}

/-- Principal symbol of the quadratic boundary measurement in
coordinates, including the induced boundary density. -/
def boundaryPrincipalDensitySymbol (h : Mat m) (ξ : X m) : ℝ :=
  Real.sqrt h.det * Real.sqrt (metricPair (fun _ => h⁻¹) 0 ξ ξ)

theorem boundaryPrincipalDensitySymbol_sq {h : Mat m} (hp : h.PosDef) (ξ : X m) :
    boundaryPrincipalDensitySymbol h ξ ^ 2 = h.det * metricPair (fun _ => h⁻¹) 0 ξ ξ := by
  rw [boundaryPrincipalDensitySymbol, mul_pow, Real.sq_sqrt hp.det_pos.le,
    Real.sq_sqrt (metricPair_nonneg_of_posDef hp.inv ξ)]

theorem boundaryMetric_eq_of_principalDensitySymbol_eq (hm : 2 ≤ m)
    {h₁ h₂ : Mat m} (hp₁ : h₁.PosDef) (hp₂ : h₂.PosDef)
    (hEq : ∀ ξ, boundaryPrincipalDensitySymbol h₁ ξ = boundaryPrincipalDensitySymbol h₂ ξ) :
    h₁ = h₂ := by
  apply boundaryMetric_eq_of_densitySymbolSq_eq hm hp₁ hp₂
  intro ξ
  rw [← boundaryPrincipalDensitySymbol_sq hp₁ ξ, ← boundaryPrincipalDensitySymbol_sq hp₂ ξ, hEq ξ]

/-- The contribution of the highest normal metric jet to the symbol on
a unit tangential direction. In this normalization the principal root
`ρ` is one. -/
def highestNormalSymbolTerm (k : ℕ) (h A : Mat m) (v : X m) : ℝ :=
  ((h⁻¹ * A).trace - metricPair (fun _ => A) 0 v v) / (4 * (2 : ℝ) ^ (k - 1))

/-- The descending symbol equations determine every normal jet once
their lower-order remainders agree whenever the earlier jets agree
as functions of the boundary point. -/
theorem boundary_jets_eq_of_symbolRecurrence {Z : Type*} (hm : 2 ≤ m) {V : Set Z}
    (J₁ J₂ : ℕ → Z → Mat m)
    (hP₁ : ∀ z ∈ V, (J₁ 0 z).PosDef) (hP₂ : ∀ z ∈ V, (J₂ 0 z).PosDef)
    (hS₁ : ∀ k z, z ∈ V → (J₁ k z).IsSymm) (hS₂ : ∀ k z, z ∈ V → (J₂ k z).IsSymm)
    (hLead : ∀ z ∈ V, ∀ ξ,
      boundaryPrincipalDensitySymbol (J₁ 0 z) ξ = boundaryPrincipalDensitySymbol (J₂ 0 z) ξ)
    (R₁ R₂ : ℕ → Z → X m → ℝ)
    (hR : ∀ k > 0, (∀ j < k, EqOn (J₁ j) (J₂ j) V) →
      ∀ z ∈ V, ∀ v, R₁ k z v = R₂ k z v)
    (hSymbol : ∀ k > 0, ∀ z ∈ V, J₁ 0 z = J₂ 0 z →
      ∀ v : X m, metricPair (fun _ => J₁ 0 z) 0 v v = 1 →
        highestNormalSymbolTerm k (J₁ 0 z) (J₁ k z) v + R₁ k z v =
        highestNormalSymbolTerm k (J₂ 0 z) (J₂ k z) v + R₂ k z v) :
    ∀ k, EqOn (J₁ k) (J₂ k) V := by
  have hBase : EqOn (J₁ 0) (J₂ 0) V := by
    intro z hz
    exact boundaryMetric_eq_of_principalDensitySymbol_eq hm (hP₁ z hz) (hP₂ z hz) (hLead z hz)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · simpa only [hk] using hBase
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    intro z hz
    let D := J₁ k z - J₂ k z
    have hD : D.IsSymm := (hS₁ k z hz).sub (hS₂ k z hz)
    have hZero : D = 0 := by
      apply normalJet_eq_zero_of_trace_direction_eq hm (hP₁ z hz) hD
      intro v hv
      have h := hSymbol k hkpos z hz (hBase hz) v hv
      rw [hR k hkpos ih z hz v, ← hBase hz, add_left_inj] at h
      have hN : 4 * (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
      have he := (div_left_inj' hN).mp h
      change ((J₁ 0 z)⁻¹ * D).trace = _
      unfold D
      rw [Matrix.mul_sub, Matrix.trace_sub]
      have hPair : metricPair (fun _ => J₁ k z - J₂ k z) 0 v v =
          metricPair (fun _ => J₁ k z) 0 v v - metricPair (fun _ => J₂ k z) 0 v v := by
        simp only [metricPair, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [hPair]
      linarith
    exact sub_eq_zero.mp hZero

end CalderonPatch
