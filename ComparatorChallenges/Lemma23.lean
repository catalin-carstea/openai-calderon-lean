module

public import Proof.CalderonPatch.NativeCapSourceJets
public import Proof.CalderonPatch.NativeInverseRegularityProof

public section

open Set
open scoped ContDiff Manifold
open CalderonN (X InteriorMetricChart)
open CalderonPatch

namespace CalderonPaper

local notation "J" m => 𝓡∂ (m+1)
local notation "Source[" m "," M "]" => smoothSourceSubmodule (m := m) (M := M)
local notation "inverse[" D "]" => DirichletData.smoothInverse D (nativeInverseRegularity D)

/-- Lemma 2.3 of the September 24, 2026 manuscript. Test sources are
smooth native functions whose support is contained in the given open set.
The coordinates for each second jet are centered at the evaluation point. -/
theorem lemma23 {m : ℕ} (hn : 2 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (J m) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (D : DirichletData m M)
    (U : Set M) (hU : IsOpen U) (hUne : U.Nonempty) (hUCompact : IsCompact (closure U))
    (hUInt : closure U ⊆ (J m).interior M) :
    (∀ f : Source[m, M], tsupport (f : M → ℝ) ⊆ U →
      Continuous (inverse[D] f) ∧ EqOn (inverse[D] f) 0 ((J m).boundary M)) ∧
    (∀ p ∈ (J m).interior M,
      ∃ f : Source[m, M], tsupport (f : M → ℝ) ⊆ U ∧ inverse[D] f p ≠ 0) ∧
    (∀ p ∈ (J m).interior M, ∀ q ∈ (J m).interior M, p ≠ q →
      ∃ f : Source[m, M], tsupport (f : M → ℝ) ⊆ U ∧ inverse[D] f p ≠ inverse[D] f q) ∧
    (∀ A : InteriorMetricChart (J m) D.volume (nativeLaplace D.metric),
      A.chart.source ⊆ (J m).interior M \ closure U →
      ∀ h0 : (0 : X (m+1)) ∈ A.chart.target,
        range (fun f : { f : Source[m, M] // tsupport (f : M → ℝ) ⊆ U } =>
          smoothSecondJet A.chart.open_target h0 (inverse[D] f.val ∘ A.chart.symm)
            (((D.smoothInverse_spec (nativeInverseRegularity D) f.val).1.comp_contMDiffOn
              A.smooth_inverse).contDiffOn)) = (laplaceOnSecondJet A.metric 0).ker) := sorry

end CalderonPaper
