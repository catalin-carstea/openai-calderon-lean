module

public import Proof.Manuscript.MovingTrace.ActualCollarWaveResidual
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2800000

open CalderonN Set Finset
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer

variable {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]

/-- For all finite truncations, the true split operator produces the
remainder amplitudes simultaneously on its normal segment domain. -/
theorem splitOperatorLayerCoefficients_exists_TaylorRemainders
    {O : Set ((P × X n) × ℝ)} (hO : IsOpen O) {U : Set (P × X n)}
    (hFace : MapsTo (fun p : P × X n => (p,(0:ℝ))) U O)
    (A : (P × X n) × ℝ → Mat n)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p => A p i j) O)
    (hSym : ∀ p ∈ O, ∀ i j, A p i j = A p j i)
    (hApos : ∀ p ∈ U, (A (p,0)).PosDef)
    (τ : (P × X n) × ℝ → ℝ) (hτ : ContDiffOn ℝ ∞ τ O)
    (b : (P × X n) × ℝ → I n → ℝ) (hb : ∀ i, ContDiffOn ℝ ∞ (fun p => b p i) O)
    (ξ : P → X n) (hξ : ContDiff ℝ ∞ ξ) (hξ₀ : ∀ p ∈ U, ξ p.1 ≠ 0) (M : ℕ) :
    let W := {q : (P × X n) × ℝ | ∀ s ∈ Icc (0 : ℝ) 1, (q.1,s*q.2) ∈ O}
    let B := splitOperatorLayerCoefficients hO hFace A hA hSym hApos τ hτ b hb ξ hξ hξ₀
    let C (p : P) := B.angularSlice p (fun i => ξ p i) (fun _ _ => rfl)
    IsOpen W ∧
      ∃ (RA : ParametricLayerCoefficients.RemainderMatrix n P)
        (Rτ : (P × X n) × ℝ → ℂ) (Rb : ParametricLayerCoefficients.RemainderDrift n P),
        (∀ i l, ContDiffOn ℝ ∞ (fun q => RA q i l) W) ∧
        ContDiffOn ℝ ∞ Rτ W ∧ (∀ i, ContDiffOn ℝ ∞ (fun q => Rb q i) W) ∧
        ∀ (p : P) (x : X n) (t : ℝ), ((p,x),t) ∈ W →
          (Matrix.of (fun i l => (A ((p,x),t) i l : ℂ)) - (C p).matrixTaylor M x t =
            ((t : ℂ)^(M+1)) • RA ((p,x),t)) ∧
          ((τ ((p,x),t) : ℂ) - (C p).normalTaylor M x t = (t : ℂ)^(M+1) * Rτ ((p,x),t)) ∧
          ((fun i => (b ((p,x),t) i : ℂ)) - (C p).tangentTaylor M x t =
            ((t : ℂ)^(M+1)) • Rb ((p,x),t)) := by
  dsimp only
  let W := {q : (P × X n) × ℝ | ∀ s ∈ Icc (0 : ℝ) 1, (q.1,s*q.2) ∈ O}
  let B := splitOperatorLayerCoefficients hO hFace A hA hSym hApos τ hτ b hb ξ hξ hξ₀
  let C (p : P) := B.angularSlice p (fun i => ξ p i) (fun _ _ => rfl)
  obtain ⟨hW,Rτ,hRτ,hGτ⟩ := collarTaylorCoefficient_exact_gap hO hτ M
  have hRA (i l : I n) := (collarTaylorCoefficient_exact_gap hO (hA i l) M).2
  have hRb (i : I n) := (collarTaylorCoefficient_exact_gap hO (hb i) M).2
  choose RA hRA hGA using hRA
  choose Rb hRb hGb using hRb
  refine ⟨hW, (fun q => Matrix.of (fun i l => RA i l q)), Rτ, (fun q i => Rb i q), hRA, hRτ, hRb, ?_⟩
  intro p x t ht
  refine ⟨?_,?_,?_⟩
  · ext i l
    exact hGA i l ((p,x),t) ht
  · exact hGτ ((p,x),t) ht
  · funext i
    exact hGb i ((p,x),t) ht

end CalderonPatch.BoundaryLayer
