module

public import Proof.CalderonPatch.KernelJetTransposition
public import Mathlib.Analysis.Matrix.Normed

import Mathlib.Topology.Algebra.Module.FiniteDimension

public section

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Manifold Matrix.Norms.Elementwise

namespace CalderonPatch

open CalderonN (X InteriorMetricChart IsDirichletGreenKernel)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n

/-- A fixed finite-order estimate for the inverse's second jet on
coordinate tests gives continuity of every transposed jet functional. -/
theorem continuous_greenInverseSecondJet_of_testBound
    {g : SmoothMetric n M} {μ : Measure M} {G : M × M → ℝ}
    {K : Compacts (X n)} (C : InteriorMetricChart J μ (nativeLaplace g))
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (hK : (K : Set (X n)) ⊆ C.chart.target) (h0 : (0 : X n) ∈ C.chart.target)
    (hSmooth : ∀ f : 𝓓_{K}(X n, ℝ), ContDiffOn ℝ ∞ (greenInverseChart C G f) C.chart.target)
    (hBound : ∃ (orders : Finset ℕ) (B : ℝ), 0 ≤ B ∧
      ∀ f : 𝓓_{K}(X n, ℝ),
        ‖smoothSecondJet C.chart.open_target h0 (greenInverseChart C G f) (hSmooth f)‖ ≤
          B * (orders.sup fun i => N[ℝ]_{K, i}) f)
    (D : ScalarSecondJet n →ₗ[ℝ] ℝ) :
    Continuous (fun f : 𝓓_{K}(X n, ℝ) =>
      -D (smoothSecondJet C.chart.open_target h0 (greenInverseChart C G f) (hSmooth f))) := by
  let u := greenInverseChartLinear C hG hK
  have hUS (f : 𝓓_{K}(X n, ℝ)) : ContDiffOn ℝ ∞ (u f) C.chart.target := by
    simpa only [u, greenInverseChartLinear_apply] using hSmooth f
  let jet := sourceSecondJet C.chart.open_target h0 u hUS
  have hJet (f : 𝓓_{K}(X n, ℝ)) :
      jet f = smoothSecondJet C.chart.open_target h0 (greenInverseChart C G f) (hSmooth f) :=
    (sourceSecondJet_apply _ _ u hUS f).trans
      (smoothSecondJet_congr_germ _ _ _ _ (hUS f) (hSmooth f)
        (Filter.Eventually.of_forall (congrFun (greenInverseChartLinear_apply C hG hK f))))
  have hJetBound : ∃ (orders : Finset ℕ) (B : ℝ), 0 ≤ B ∧
      ∀ f : 𝓓_{K}(X n, ℝ), ‖jet f‖ ≤ B * (orders.sup fun i => N[ℝ]_{K, i}) f := by
    simpa only [hJet] using hBound
  obtain ⟨orders,B,hB,hBoundJet⟩ := hJetBound
  have hCont : Continuous jet :=
    WithSeminorms.continuous_normedSpace_rng (ScalarSecondJet n)
      (ContDiffMapSupportedIn.withSeminorms ℝ (X n) ℝ ⊤ K) jet ⟨orders,⟨B,hB⟩,hBoundJet⟩
  have hC : Continuous (fun f : 𝓓_{K}(X n, ℝ) => -D (jet f)) :=
    D.continuous_of_finiteDimensional.neg.comp hCont
  exact hC.congr (fun f => congrArg (fun j => -D j) (hJet f))

end CalderonPatch
