module

public import Proof.Manuscript.ScalarCrossExtension
public import Proof.Manuscript.ScalarUniformRestriction

import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ContDiff ENNReal Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

open Classical in
set_option maxHeartbeats 4200000 in
/-- The two-arm series estimate is uniform for finite coefficient budgets
and a uniform positive exponent margin. -/
theorem exists_numeric_scalar_crossExtension
    {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hConn₁ : IsConnected D₁) (hConn₂ : IsConnected D₂)
    (hD₂finite : (volume : Measure (X n)) D₂ ≠ ⊤)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hSne₁ : S₁.Nonempty) (hSne₂ : S₂.Nonempty)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hSc₁ : IsCompact (closure S₁)) (hS₁D₁ : closure S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂)
    (hO₁D₁ : O₁ ⊆ D₁) (hO₂D₂ : O₂ ⊆ D₂)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (β : ℝ) (hβ : 0 < β) {K : Set (X n × X n)} (hK : K ⊆ O₁ ×ˢ O₂)
    (hKc : IsCompact K) (m : ℕ) :
    ∃ N : ℕ, ∀ a A : ℝ, 0 < a → 0 < A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ γ₁ γ₂ : ℝ, 0 < γ₂ → γ₂ ≤ 1 → 1 + β ≤ γ₁ + γ₂ →
      ∀ (L₁ L₂ : ScalarElliptic n), L₁.SmoothOn D₁ → L₂.SmoothOn D₂ →
        L₁.CoefficientBound D₁ a A N → L₂.CoefficientBound D₂ a A N →
        L₁.Interpolates D₁ S₁ O₁ C₁ γ₁ → L₂.Interpolates D₂ S₂ O₂ C₂ γ₂ →
        ∀ F (M : ℝ), CrossData L₁ L₂ D₁ D₂ S₁ S₂ F M →
        ∃ G, CrossExtension L₁ L₂ S₁ S₂ O₁ O₂ F G ∧
          ∀ j ≤ m, ∀ z ∈ K, ‖iteratedFDeriv ℝ j G z‖ ≤ C*M := by
  classical
  obtain ⟨s,hs⟩ := exists_nat_gt (((n+3 : ℕ) : ℝ) / β)
  have hRank : ((n+3 : ℕ) : ℝ) < s*β := (div_lt_iff₀ hβ).mp hs
  let d := (fullCoordinateWord (n+3)).length
  let N := d + max m (s+1) + 2
  refine ⟨N,?_⟩
  intro a A ha hA
  have hRorder : d + (s+1) + 2 ≤ N := by dsimp [N]; omega
  have hJorder (r : ℕ) (hr : r ≤ m) : d + r + 2 ≤ N := by dsimp [N]; omega
  have hSD₁ : S₁ ⊆ D₁ := subset_closure.trans hS₁D₁
  obtain ⟨B,N₁,A₀,_,hApprox⟩ := exists_numeric_counted_scalar_restriction hD₁ hS₁.measurableSet
    hSc₁ subset_closure hS₁D₁ s ha hA
  obtain ⟨P,hP,hSpectra⟩ := exists_uniform_countedSubspaceSpectrum
    (N := N₁) (A₀ := A₀) (B := B) hβ hRank
  let Index₁ := {L : ScalarElliptic n // L.SmoothOn D₁ ∧ L.CoefficientBound D₁ a A N}
  let Index₂ := {L : ScalarElliptic n // L.SmoothOn D₂ ∧ L.CoefficientBound D₂ a A N}
  let g₁ (p : Index₁) := p.1
  let g₂ (p : Index₂) := p.1
  choose J hJ hSeries using (fun j : Fin (m+1) => exists_scalar_productSeries_jetBound_family
    hO₁ hO₂ g₁ g₂ hKc hK j
    (fun H hH hHO r hr => by
      obtain ⟨C,hC,h⟩ := exists_numeric_scalar_interior_jet_bound hO₁ hH hHO r ha hA
      have hr' : r ≤ m := hr.trans (Nat.le_of_lt_succ j.isLt)
      exact ⟨C,hC,fun p u _ => h p.1 (p.2.1.restrict hO₁D₁)
        (p.2.2.mono hO₁D₁ (hJorder r hr')) u⟩)
    (fun H hH hHO r hr => by
      obtain ⟨C,hC,h⟩ := exists_numeric_scalar_interior_jet_bound hO₂ hH hHO r ha hA
      have hr' : r ≤ m := hr.trans (Nat.le_of_lt_succ j.isLt)
      exact ⟨C,hC,fun p u _ => h p.1 (p.2.1.restrict hO₂D₂)
        (p.2.2.mono hO₂D₂ (hJorder r hr')) u⟩))
  let C₀ := ∑ j, J j
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun j _ => hJ j
  refine ⟨C₀ * (C₁*C₂*P),by positivity,?_⟩
  intro γ₁ γ₂ hγ₂ hγ₂' hMargin L₁ L₂ hL₁ hL₂ hCoef₁ hCoef₂ hI₁ hI₂ F M hData
  let H₁ := scalarSolutionL2 hD₁ hL₁
  let R := closedRestrict H₁ hSD₁
  obtain ⟨ι,w,μ,hCount,hμ,hμ₁,hEigen,hGram,hSum,hSumP⟩ := hSpectra R (norm_closedRestrict_le H₁ hSD₁)
    (closedRestrict_injective hD₁ hConn₁ hL₁ hS₁ hSne₁ hSD₁)
    (hApprox L₁ hL₁ (hCoef₁.mono Subset.rfl hRorder))
  have hPower (i : ι) : μ i ^ (γ₁+γ₂-1) ≤ μ i ^ β :=
    Real.rpow_le_rpow_of_exponent_ge (hμ i) (hμ₁ i) (by linarith)
  have hsum' := Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (hμ i).le (γ₁+γ₂-1)) hPower hSum
  have hSumP' : (∑' i, μ i ^ (γ₁+γ₂-1)) ≤ P :=
    (hsum'.tsum_le_tsum hPower hSum).trans hSumP
  let T : Set (Set (X n × X n) × ℕ) := {p | p.1 = K ∧ p.2 ≤ m}
  have hJet (H : Set (X n × X n)) (_ : H ⊆ O₁ ×ˢ O₂) (_ : IsCompact H)
      (j : ℕ) (hj : (H,j) ∈ T) :
      0 ≤ C₀ ∧ ScalarSeriesJetEstimate (D₁ := O₁) (D₂ := O₂) L₁ L₂ H j C₀ := by
    have hh : H = K := hj.1
    subst H
    let j' : Fin (m+1) := ⟨j,Nat.lt_succ_of_le hj.2⟩
    have hj' : J j' ≤ C₀ := Finset.single_le_sum (fun j _ => hJ j) (Finset.mem_univ j')
    refine ⟨hC₀,?_⟩
    intro ι f b a c ha hc hfa hbc hnorm z hz
    exact (hSeries j' ⟨L₁,hL₁,hCoef₁⟩ ⟨L₂,hL₂,hCoef₂⟩ f b a c ha hc hfa hbc hnorm z hz).trans
      (mul_le_mul_of_nonneg_right hj' (tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  obtain ⟨G,hG,hBound⟩ := scalar_crossExtension_of_spectrum_and_jets hD₁ hD₂ hConn₂
    hD₂finite hS₁ hS₂ hSne₂ hO₁ hO₂ hSD₁ hS₂D₂ hO₁D₁ hO₂D₂ hL₁ hL₂
    hC₁ hC₂ hγ₂ hγ₂' hI₁ hI₂ ⟨ι,w,μ,hCount,hμ,hEigen,hGram,hsum',hSumP'⟩ hJet F M hData
  exact ⟨G,hG,fun j hj => hBound K hK hKc j ⟨rfl,hj⟩⟩

end CalderonPaper.ScalarElliptic
