module

public import Proof.CalderonPatch.GreenChartSourceRepresentation
public import Proof.CalderonPatch.GreenInverseJetContinuity

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Manifold Matrix.Norms.Elementwise Topology

namespace CalderonPatch

set_option autoImplicit false

open CalderonN (X InteriorMetricChart)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Y" => X (m+1)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)
variable (C : InteriorMetricChart (𝓡∂ (m+1)) D.volume (nativeLaplace D.metric))
variable {K : Compacts (X (m+1))} (hK : (K : Set (X (m+1))) ⊆ C.chart.target)

/-- Extension of a supported coordinate test to a smooth native source. -/
@[expose] def smoothChartSource (f : 𝓓_{K}(Y, ℝ)) : Source :=
  chartTestSource C f f.contDiff f.compact_supp (f.tsupport_subset.trans hK)

variable {G : M × M → ℝ}
variable (hRep : ∀ q ∈ (𝓡∂ (m+1)).interior M, ∀ f : smoothSourceSubmodule (m := m) (M := M),
    Integrable (fun p => G (p,q) * f p) D.volume ∧
    (∫ p, G (p,q) * f p ∂D.volume) = D.smoothInverse h f q)

include hRep in
/-- The existing chart inverse is the same weak inverse on its full chart. -/
theorem greenInverseChart_eqOn_smoothInverse (f : 𝓓_{K}(Y, ℝ)) :
    EqOn (greenInverseChart C G f)
      (D.smoothInverse h (smoothChartSource C hK f) ∘ C.chart.symm) C.chart.target := by
  intro z hz
  rw [greenInverseChart_apply C (G := G) f hz]
  exact (hRep _ (C.source_interior (C.chart.map_target hz)) (smoothChartSource C hK f)).2

private theorem contDiffOn_smoothInverse_chart (f : 𝓓_{K}(Y, ℝ)) :
    ContDiffOn ℝ ∞ (D.smoothInverse h (smoothChartSource C hK f) ∘ C.chart.symm) C.chart.target := by
  have hSmooth := (D.smoothInverse_spec h (smoothChartSource C hK f)).1
  exact (hSmooth.comp_contMDiffOn C.smooth_inverse).contDiffOn

include hK hRep in
/-- Native smooth-source regularity gives precisely the smoothness
required by the checked Green jet transposition. -/
theorem contDiffOn_greenInverseChart_of_native (f : 𝓓_{K}(Y, ℝ)) :
    ContDiffOn ℝ ∞ (greenInverseChart C G f) C.chart.target :=
  (contDiffOn_smoothInverse_chart h C hK f).congr
    (greenInverseChart_eqOn_smoothInverse h C hK hRep f)

end CalderonPatch
