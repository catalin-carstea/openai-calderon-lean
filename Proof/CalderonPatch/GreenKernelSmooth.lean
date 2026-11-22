module

public import Proof.CalderonPatch.GreenOffDiagonalConstruction
public import Proof.CalderonPatch.HarmonicRieszEvaluation

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold RealInnerProductSpace Topology

namespace CalderonPatch

open CalderonN (X harmonicRiesz harmonicL2Space)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Y" => X (m+1)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)

local notation "L²" => Lp ℝ 2 D.volume

namespace GreenEvaluationChart

variable (C : GreenEvaluationChart D)

local notation "𝒜" => harmonicL2Space C.chart.open_target C.metricChart.smooth_metric

omit [T2Space M] [CompactSpace M] [PreconnectedSpace M] in
theorem evaluationSource_smooth :
    ContDiffOn ℝ ∞ C.evaluationSource C.chart.target := by
  unfold evaluationSource
  exact ((C.pushSource.comp (𝒜).toSubmodule.subtypeL).contDiff.comp_contDiffOn
    (CalderonN.contDiffOn_harmonicRiesz C.chart.open_target C.metricChart.smooth_metric))

end GreenEvaluationChart

theorem nativeGreenCandidate_smooth_off_diagonal :
    ContMDiffOn ((J).prod J) R ∞ (nativeGreenCandidate h)
      {z | z.1 ∈ (J).interior M ∧ z.2 ∈ (J).interior M ∧ z.1 ≠ z.2} := by
  apply contMDiffOn_of_locally_contMDiffOn
  rintro ⟨x,q⟩ ⟨hx,hq,hne⟩
  obtain ⟨C,E,hCx,hEq,hDisj⟩ := exists_disjoint_poleCharts (D := D) hx hq hne
  let W := C.chart.source ×ˢ E.chart.source
  refine ⟨W,C.chart.open_source.prod E.chart.open_source,⟨hCx,hEq⟩,?_⟩
  suffices ContMDiffOn ((J).prod J) R ∞ (nativeGreenCandidate h) W from this.mono inter_subset_right
  have hC : ContMDiffOn J 𝓘(ℝ,L²) ∞ (C.evaluationSource ∘ C.chart) C.chart.source :=
    C.evaluationSource_smooth.contMDiffOn.comp C.smooth C.chart.mapsTo
  have hE : ContMDiffOn J 𝓘(ℝ,L²) ∞
      ((D.weakInverseL2 : L² → L²) ∘ E.evaluationSource ∘ E.chart) E.chart.source :=
    (D.weakInverseL2.contDiff.comp_contDiffOn E.evaluationSource_smooth).contMDiffOn.comp
      E.smooth E.chart.mapsTo
  have hInner : ContMDiff ((𝓘(ℝ,L²)).prod 𝓘(ℝ,L²)) R ∞
      (fun p : L² × L² => ⟪p.1,p.2⟫) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (contDiff_inner : ContDiff ℝ ∞ (fun p : L² × L² => ⟪p.1,p.2⟫)).contMDiff
  refine (hInner.comp_contMDiffOn (hC.prodMap hE)).congr (fun p hp => ?_)
  exact nativeGreenCandidate_pair_chart h C E hDisj hp.1 hp.2

end CalderonPatch
