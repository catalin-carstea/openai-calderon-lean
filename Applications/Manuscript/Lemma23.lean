module

public import Proof.Manuscript.Lemma23

public section

open Set
open scoped ContDiff Manifold
open CalderonN (X InteriorMetricChart)
open CalderonPatch

namespace CalderonPaper

local notation "J" m => 𝓡∂ (m+1)
local notation "Source[" m "," M "]" => smoothSourceSubmodule (m := m) (M := M)
local notation "inverse[" D "]" => DirichletData.smoothInverse D (nativeInverseRegularity D)

theorem realizesSupportedHarmonicJet {m : ℕ} (hn : 2 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (J m) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (D : DirichletData m M)
    (U : Set M) (hU : IsOpen U) (hUne : U.Nonempty) (hUCompact : IsCompact (closure U))
    (hUInt : closure U ⊆ (J m).interior M)
    (A : InteriorMetricChart (J m) D.volume (nativeLaplace D.metric))
    (hA : A.chart.source ⊆ (J m).interior M \ closure U)
    (h0 : (0 : X (m+1)) ∈ A.chart.target)
    (v : ScalarSecondJet (m+1)) (hv : v ∈ (laplaceOnSecondJet A.metric 0).ker) :
    ∃ f : { f : Source[m, M] // tsupport (f : M → ℝ) ⊆ U },
      smoothSecondJet A.chart.open_target h0 (inverse[D] f.val ∘ A.chart.symm)
        (((D.smoothInverse_spec (nativeInverseRegularity D) f.val).1.comp_contMDiffOn
          A.smooth_inverse).contDiffOn) = v := by
  have h := (lemma23 hn D U hU hUne hUCompact hUInt).2.2.2 A hA h0
  change v ∈ ((laplaceOnSecondJet A.metric 0).ker : Set _) at hv
  rw [← h] at hv
  exact hv

end CalderonPaper
