module

public import Proof.Manuscript.ScalarRestriction
public import Proof.Manuscript.ScalarUniformJets
public import Proof.Manuscript.ScalarRestrictionSpectrum

import all Proof.CalderonN.HarmonicTaylorApproximation
import Proof.CalderonN.CountedFloorGrid
import Proof.CalderonN.InteriorJetCutoff
import Proof.CalderonN.CrossRestrictionSpectrum
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory Metric CalderonN LocalMetricExtension
open scoped ContDiff Topology ENNReal

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

set_option maxHeartbeats 2400000 in
/-- The counted restriction constants are uniform under a finite
coefficient budget. For Taylor order `s`, only order `s+1` needs a common
bound. The fixed per-operator lower-order jet maps are unchanged. -/
theorem exists_numeric_counted_scalar_restriction {D S K : Set (X n)}
    (hD : IsOpen D) (hS : MeasurableSet S) (hK : IsCompact K)
    (hSK : S ⊆ K) (hKD : K ⊆ D) (s : ℕ)
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    ∃ (B : ℝ) (N A₀ : ℕ), 0 ≤ B ∧ ∀ (L : ScalarElliptic n) (hL : L.SmoothOn D),
      L.CoefficientBound D a A ((fullCoordinateWord (n+3)).length + (s+1) + 2) →
      ∀ r : ℕ, A₀ ≤ r →
      ∃ P : scalarSolutionL2 hD hL →L[ℝ] ChartL2 S,
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ N * r ^ (n+3) ∧
        ‖closedRestrict (scalarSolutionL2 hD hL) (hSK.trans hKD) - P‖ * (r : ℝ)^s ≤ B := by
  let : NeZero (n+3) := ⟨by omega⟩
  let : IsFiniteMeasure ((volume : Measure (X n)).restrict S) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hSK).trans_lt hK.measure_lt_top).ne
  let U := augmentedDomain D
  let V := augmentedObservation S
  have hU : IsOpen U := augmentedDomain_open hD
  have hV : MeasurableSet V := augmentedObservation_measurable hS
  obtain ⟨J,hJ,hVJ,hJU⟩ := augmentedObservation_compactBuffer hK hSK hKD
  obtain ⟨d,hd,hdD⟩ := hJ.exists_cthickening_subset_open hU hJU
  have : IsFiniteMeasure ((volume : Measure (X (n+3))).restrict V) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hVJ).trans_lt hJ.measure_lt_top).ne
  have hSub : V ⊆ U := hVJ.trans hJU
  let N₀ := (fullCoordinateWord (n+3)).length + (s+1)
  let Index := {L : ScalarElliptic n // L.SmoothOn D ∧ L.CoefficientBound D a A (N₀+2)}
  let g (l : Index) := l.1.augmentedMetric
  have hG (l : Index) : SmoothMetric U (g l) := augmentedMetric_smoothOnDomain hD l.2.1
  have hJet (l : Index) : HarmonicInteriorJets U (g l) := harmonicInteriorJets_of_smoothMetric hU (hG l)
  obtain ⟨lam,Ma,hlam,_,hBudget⟩ := exists_numeric_augmented_divergence_budget (n := n) a A ha hA N₀
  obtain ⟨C,hC,hDeriv⟩ := exists_numeric_harmonic_interior_jet_bound
    hU hJ.cthickening hdD (s+1) (Ma := Ma) hlam
  have hEstimate (l : Index) :=
    hDeriv (g l) (hG l)
      (fun z hz => (hBudget l.1 hD l.2.1 l.2.2).1 z hz.1)
      (fun z hz => (hBudget l.1 hD l.2.1 l.2.2).2 z hz.1)
  obtain ⟨B,N,A₀,hApprox⟩ := counted_approx_of_cell_taylor_family
    (fun l => harmonicRestrict hU (hG l) hSub) V J hV hVJ hJ d hd s
    (HarmonicTaylor.cellTaylorNormFactor V s * C)
    (mul_nonneg (HarmonicTaylor.cellTaylorNormFactor_nonneg V s) hC)
      (fun l => HarmonicTaylor.cell_taylor_finite_rank_of_bound U hU (g l) (hG l) (hJet l)
        V hV hSub (cthickening d J) hdD s C hC (hEstimate l))
  refine ⟨scalarRestrictionCost hS * max B 0,N,A₀,
    mul_nonneg (scalarRestrictionCost_nonneg hS) (le_max_right _ _),?_⟩
  intro L hL hCoeff
  exact counted_scalar_restriction_of_counted_harmonic hD hL hS (hSK.trans hKD)
    (hApprox ⟨L,hL,hCoeff⟩)

end CalderonPaper.ScalarElliptic
