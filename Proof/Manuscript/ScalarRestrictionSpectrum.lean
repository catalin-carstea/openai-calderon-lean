module

public import Proof.Manuscript.ScalarRestriction
public import Proof.Manuscript.ScalarCrossSlices

import Proof.CalderonN.CrossSpectral
import Mathlib.Tactic

public section

open Set Filter Metric MeasureTheory CalderonN LocalMetricExtension
open scoped ENNReal

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

-- The countability argument is the support proof of the released
-- CrossRestrictionSpectrum, independent of the operator.
private theorem countable_of_positive_sum {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hs : Summable a) : Countable ι := by
  have hnorm : Summable (fun i => ‖a i‖) := hs.norm
  have hc : (Function.support (fun i => ‖a i‖ₑ)).Countable :=
    Summable.countable_support_ennreal (tsum_enorm_ne_top_iff_summable_norm.mpr hnorm)
  have he : Function.support (fun i => ‖a i‖ₑ) = univ := by
    ext i
    simp [Function.mem_support, (ha i).ne']
  exact countable_univ_iff.mp (he ▸ hc)

private theorem compact_of_counted_approx
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (R : E →L[ℝ] F) {s A₀ : ℕ} {B : ℝ} (hs : s ≠ 0)
    (happ : ∀ A : ℕ, A₀ ≤ A → ∃ T : E →L[ℝ] F,
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        ‖R - T‖ * (A : ℝ)^s ≤ B) :
    IsCompactOperator R := by
  apply isCompactOperator_of_finiteRank_approx
  intro ε hε
  obtain ⟨a,ha⟩ := exists_nat_gt (max 1 (B / ε))
  let A := max A₀ a
  have haA : (a : ℝ) ≤ (A : ℝ) := by exact_mod_cast le_max_right A₀ a
  have hA₁ : (1 : ℝ) ≤ A := (le_max_left _ _).trans (ha.le.trans haA)
  have hB : B / ε ≤ (A : ℝ) ^ s :=
    (le_max_right _ _).trans (ha.le.trans (haA.trans (le_self_pow₀ hA₁ hs)))
  obtain ⟨T,hT,he⟩ := happ A (le_max_left _ _)
  refine ⟨T,hT,le_of_mul_le_mul_right ?_ (show 0 < (A : ℝ) ^ s by positivity)⟩
  exact he.trans (by simpa only [mul_comm] using (div_le_iff₀ hε).mp hB)

open Classical in
set_option maxHeartbeats 1600000 in
/-- The power-sum constant of a counted family is chosen before any
Hilbert spaces, compact operators, or bases. -/
theorem exists_uniform_countedSubspaceSpectrum
    {q s N A₀ : ℕ} {B β : ℝ} (hβ : 0 < β) (hMargin : (q : ℝ) < s * β) :
    ∃ P : ℝ, 0 ≤ P ∧
    ∀ {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (R : E →L[ℝ] F), ‖R‖ ≤ 1 → Function.Injective R →
      (∀ A : ℕ, A₀ ≤ A → ∃ T : E →L[ℝ] F,
        FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
          Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ N * A ^ q ∧
          ‖R - T‖ * (A : ℝ)^s ≤ B) →
      ∃ (ι : Type) (w : HilbertBasis ι ℝ E) (μ : ι → ℝ),
        Countable ι ∧ (∀ i, 0 < μ i) ∧ (∀ i, μ i ≤ 1) ∧
        (∀ i, (R.adjoint ∘L R) (w i) = μ i ^ 2 • w i) ∧
        (∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) ∧
        Summable (fun i => μ i ^ β) ∧ (∑' i, μ i ^ β) ≤ P := by
  classical
  have hs : s ≠ 0 := by
    intro h
    rw [h,Nat.cast_zero,zero_mul] at hMargin
    exact (not_lt_of_ge (Nat.cast_nonneg _)) hMargin
  obtain ⟨P,hP,hSum⟩ := uniform_powerSum_of_counted_approx 1 one_pos q s B N A₀ β hβ hMargin
  refine ⟨P,hP,?_⟩
  intro E F _ _ _ _ _ _ R hNorm hInj happ
  have hCompact : IsCompactOperator R := compact_of_counted_approx R hs fun A hA => by
    obtain ⟨T,hT,_,he⟩ := happ A hA
    exact ⟨T,hT,he⟩
  obtain ⟨ι,w,μ,hμ,hμR,heig,hgram⟩ := exists_gram_spectral_data R hCompact hInj
  have hμ1 (i : ι) : μ i ≤ 1 := (hμR i).trans hNorm
  obtain ⟨hsum,hPμ⟩ := hSum R w w.orthonormal μ hμ hμ1 hgram happ
  exact ⟨ι,w,μ,countable_of_positive_sum (fun i => Real.rpow_pos_of_pos (hμ i) _) hsum,
    hμ,hμ1,heig,hgram,hsum,hPμ⟩

open Classical in
set_option maxHeartbeats 1600000 in
theorem exists_countedSubspaceSpectrum
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (R : E →L[ℝ] F) (hNorm : ‖R‖ ≤ 1) (hInj : Function.Injective R)
    {q s N A₀ : ℕ} {B β : ℝ} (hβ : 0 < β) (hMargin : (q : ℝ) < s * β)
    (happ : ∀ A : ℕ, A₀ ≤ A → ∃ T : E →L[ℝ] F,
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ N * A ^ q ∧
        ‖R - T‖ * (A : ℝ)^s ≤ B) :
    ∃ P : ℝ, 0 ≤ P ∧ ∃ (ι : Type) (w : HilbertBasis ι ℝ E) (μ : ι → ℝ),
      Countable ι ∧ (∀ i, 0 < μ i) ∧ (∀ i, μ i ≤ 1) ∧
      (∀ i, (R.adjoint ∘L R) (w i) = μ i ^ 2 • w i) ∧
      (∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) ∧
      Summable (fun i => μ i ^ β) ∧ (∑' i, μ i ^ β) ≤ P := by
  obtain ⟨P,hP,h⟩ := exists_uniform_countedSubspaceSpectrum (N := N) (A₀ := A₀) (B := B) hβ hMargin
  exact ⟨P,hP,h R hNorm hInj happ⟩

open Classical in
set_option maxHeartbeats 1600000 in
/-- The actual scalar restriction has an injective compact Gram operator,
and all power sums needed by the two-arm continuation converge. -/
theorem exists_scalar_restrictionSpectrum {L : ScalarElliptic n} {D S : Set (X n)}
    (hD : IsOpen D) (hConn : IsConnected D) (hL : L.SmoothOn D) (hS : IsOpen S)
    (hSne : S.Nonempty) (hSC : IsCompact (closure S)) (hSD : closure S ⊆ D)
    {β : ℝ} (hβ : 0 < β) :
    let H := scalarSolutionL2 hD hL
    let R := closedRestrict H (subset_closure.trans hSD)
    ∃ P : ℝ, 0 ≤ P ∧ ∃ (ι : Type) (w : HilbertBasis ι ℝ H) (μ : ι → ℝ),
      Countable ι ∧ (∀ i, 0 < μ i) ∧ (∀ i, μ i ≤ 1) ∧
      (∀ i, (R.adjoint ∘L R) (w i) = μ i ^ 2 • w i) ∧
      (∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) ∧
      Summable (fun i => μ i ^ β) ∧ (∑' i, μ i ^ β) ≤ P := by
  classical
  intro H R
  obtain ⟨s,hs⟩ := exists_nat_gt (((n+3 : ℕ) : ℝ) / β)
  have hpow : ((n+3 : ℕ) : ℝ) < s*β := (div_lt_iff₀ hβ).mp hs
  obtain ⟨B,N,A₀,_,happ⟩ := exists_counted_scalar_restriction hD hL hS.measurableSet
    hSC subset_closure hSD s
  have hSD' : S ⊆ D := subset_closure.trans hSD
  exact exists_countedSubspaceSpectrum R (norm_closedRestrict_le H hSD')
    (closedRestrict_injective hD hConn hL hS hSne hSD') hβ hpow happ

end CalderonPaper.ScalarElliptic
