module

public import Proof.CalderonN.ConnectionFourthBounds
public import Proof.CalderonN.UniformThirdConnection

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/UniformFourthConnection.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def fourthConnectionBudget (dim : ℕ) (K M1 M2 M3 M4 M5 : ℝ) : ℝ :=
  (dim : ℝ)^3*fourthChristoffelBudget dim K M1 M2 M3 M4 M5

/-- Tensorize actual scalar Christoffel fourth-jet bounds using the same
    canonical coordinate bilinear atoms and shared finite-sum estimates. -/
theorem Elliptic.connection_fourth_operator_bound {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X dim)} (hy : y ∈ Ω)
    (M1 M2 M3 M4 M5 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hM4 : 0 ≤ M4) (hM5 : 0 ≤ M5)
    (hD1 : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M1)
    (hD2 : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M2)
    (hD3 : ∀ i j,‖iteratedFDeriv ℝ 3 (fun x => g x i j) y‖ ≤ M3)
    (hD4 : ∀ i j,‖iteratedFDeriv ℝ 4 (fun x => g x i j) y‖ ≤ M4)
    (hD5 : ∀ i j,‖iteratedFDeriv ℝ 5 (fun x => g x i j) y‖ ≤ M5) :
    ‖iteratedFDeriv ℝ 4 (connectionBilinear g) y‖ ≤ fourthConnectionBudget dim K M1 M2 M3 M4 M5 := by
  let C := fourthChristoffelBudget dim K M1 M2 M3 M4 M5
  let F (i j k : (I dim)) (x : (X dim)) := christoffel g x k i j • coordinateBilinearAtom i j k
  have hΓ (i j k : (I dim)) := (h.contDiffOn_christoffel hΩ hK k i j).contDiffAt (hΩ.mem_nhds hy)
  have hF (i j k : (I dim)) : ContDiffAt ℝ ∞ (F i j k) y := (hΓ i j k).smul contDiffAt_const
  have hTerm (i j k : (I dim)) : ‖iteratedFDeriv ℝ 4 (F i j k) y‖ ≤ C := by
    have hb := norm_iteratedFDeriv_smul_const_le (hΓ i j k) (coordinateBilinearAtom i j k) 4
    have hEntry := h.christoffel_fourth_fderiv_bound hΩ hK hy M1 M2 M3 M4 M5
      hM1 hM2 hM3 hM4 hM5 hD1 hD2 hD3 hD4 hD5 k i j
    exact hb.trans ((mul_le_mul (coordinateBilinearAtom_norm_le_one i j k) hEntry
      (norm_nonneg _) zero_le_one).trans_eq (one_mul C))
  change ‖iteratedFDeriv ℝ 4 (fun x => ∑ i,∑ j,∑ k,F i j k x) y‖ ≤ (dim : ℝ)^3*C
  calc
    _ ≤ ∑ i : (I dim),‖iteratedFDeriv ℝ 4 (fun x => ∑ j,∑ k,F i j k x) y‖ :=
      norm_iteratedFDeriv_finite_sum_le _ _ y 4 (fun i _ => ContDiffAt.sum
        (fun j _ => ContDiffAt.sum (fun k _ => hF i j k)))
    _ ≤ ∑ i : (I dim),∑ j : (I dim),‖iteratedFDeriv ℝ 4 (fun x => ∑ k,F i j k x) y‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_iteratedFDeriv_finite_sum_le _ _ y 4 (fun j _ => ContDiffAt.sum (fun k _ => hF i j k))
    _ ≤ ∑ i : (I dim),∑ j : (I dim),∑ k : (I dim),‖iteratedFDeriv ℝ 4 (F i j k) y‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact norm_iteratedFDeriv_finite_sum_le _ _ y 4 (fun k _ => hF i j k)
    _ ≤ ∑ _i : (I dim),∑ _j : (I dim),∑ _k : (I dim),C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hTerm i j k)))
    _ = (dim : ℝ)^3*C := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

@[expose] def backgroundFourthConnectionBudget (dim : ℕ) {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  fourthConnectionBudget dim K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩| |M ⟨4,by omega⟩| |M ⟨5,by omega⟩|

/-- The frozen finite background budget supplies the actual fourth
    connection derivative uniformly, without a chosen-frame derivative bound. -/
theorem Background.connection_fourth_derivative_budget {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ}
    {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m) {y : (X dim)} (hy : y ∈ Ω) :
    ‖iteratedFDeriv ℝ 4 (connectionBilinear g) y‖ ≤ backgroundFourthConnectionBudget dim hm K M := by
  exact h.1.connection_fourth_operator_bound hΩ hK hy
    |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩| |M ⟨4,by omega⟩| |M ⟨5,by omega⟩|
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (fun i j => (h.reference_fderiv_bound (by omega) hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_second_fderiv_bound (by omega) hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_jet_bound ⟨3,by omega⟩ hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_jet_bound ⟨4,by omega⟩ hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_jet_bound ⟨5,by omega⟩ hy i j).trans (le_abs_self _))

end CalderonN
