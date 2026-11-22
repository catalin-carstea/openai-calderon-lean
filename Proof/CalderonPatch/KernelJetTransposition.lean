module

public import Proof.CalderonPatch.PointLaplaceOrder
public import Proof.CalderonPatch.SourceJetRange
public import Proof.CalderonN.GreenRestriction

import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Manifold Topology

namespace CalderonPatch

open CalderonN (X InteriorMetricChart IsDirichletGreenKernel chartTest contMDiff_chartTest
  hasCompactSupport_chartTest tsupport_chartTest_subset laplace laplace_congrOn)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

variable {g : SmoothMetric n M} {μ : Measure M} {G : M × M → ℝ}
  {K : Compacts (X n)}

omit [NeZero n] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M] in
theorem chartTest_comp_inverse (e : OpenPartialHomeomorph M (X n)) (f : X n → ℝ) :
    EqOn (chartTest e f ∘ e.symm) f e.target := by
  intro x hx
  rw [Function.comp_apply, chartTest, indicator_of_mem (e.map_target hx), Function.comp_apply, e.right_inv hx]

omit [BorelSpace M] in
/-- The native Laplacian of a coordinate test is the extension by zero
of the chart Laplacian, including at points off the chart. -/
theorem nativeLaplace_chartTest_laplace (C : InteriorMetricChart J μ (nativeLaplace g))
    (hK : (K : Set (X n)) ⊆ C.chart.target) (f : 𝓓_{K}(X n, ℝ)) :
    nativeLaplace g (chartTest C.chart f) = chartTest C.chart (compactLaplace C.chart.open_target hK C.smooth_metric f) := by
  let e := C.chart
  have hs : tsupport (f : X n → ℝ) ⊆ e.target := f.tsupport_subset.trans hK
  have hf : ContMDiff J R ∞ (chartTest e f) := contMDiff_chartTest e C.smooth f.contDiff f.compact_supp hs
  funext p
  by_cases hp : p ∈ e.source
  · rw [C.laplace_eq _ hf p hp]
    conv_rhs => rw [chartTest, indicator_of_mem hp]
    change laplace C.metric (chartTest e f ∘ e.symm) (e p) = laplace C.metric f (e p)
    exact laplace_congrOn e.open_target (fun _ _ => rfl) (chartTest_comp_inverse e f) (e.map_source hp)
  · have hNoSupp : p ∉ tsupport (chartTest e f) := by
      intro h
      obtain ⟨x, hx, rfl⟩ := tsupport_chartTest_subset e f.compact_supp hs h
      exact hp (e.map_target (hs hx))
    have hzero : nativeLaplace g (chartTest e f) p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hNoSupp (tsupport_nativeLaplace_subset g _ h))
    rw [hzero, chartTest, indicator_of_notMem hp]

/-- The actual Green integral on chart tests, in the target coordinates. -/
def greenInverseChart (C : InteriorMetricChart J μ (nativeLaplace g)) (G : M × M → ℝ)
    (f : 𝓓_{K}(X n, ℝ)) : X n → ℝ :=
  C.chart.target.indicator (fun z => ∫ y, G (y, C.chart.symm z) * chartTest C.chart f y ∂μ)

private theorem integrable_greenInverseChart_kernel (C : InteriorMetricChart J μ (nativeLaplace g))
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (hK : (K : Set (X n)) ⊆ C.chart.target) (f : 𝓓_{K}(X n, ℝ)) {z : X n} (hz : z ∈ C.chart.target) :
    Integrable (fun y => G (y, C.chart.symm z) * chartTest C.chart f y) μ := by
  have hS := f.tsupport_subset.trans hK
  have hf := contMDiff_chartTest C.chart C.smooth f.contDiff f.compact_supp hS
  have hSupp := hasCompactSupport_chartTest C.chart f.compact_supp hS
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hSupp
  exact (hG.integrable _ (C.source_interior (C.chart.map_target hz))).mul_bdd
    hf.continuous.aestronglyMeasurable (ae_of_all _ hB)

omit [T2Space M] [BorelSpace M] in
theorem greenInverseChart_apply (C : InteriorMetricChart J μ (nativeLaplace g))
    (f : 𝓓_{K}(X n, ℝ)) {z : X n} (hz : z ∈ C.chart.target) :
    greenInverseChart C G f z = ∫ y, G (y, C.chart.symm z) * chartTest C.chart f y ∂μ :=
  indicator_of_mem hz _

/-- The inverse represented by the Green kernel is linear on tests. -/
def greenInverseChartLinear (C : InteriorMetricChart J μ (nativeLaplace g))
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (hK : (K : Set (X n)) ⊆ C.chart.target) : 𝓓_{K}(X n, ℝ) →ₗ[ℝ] (X n → ℝ) where
  toFun := greenInverseChart C G
  map_add' f h := by
    funext z
    let e := C.chart
    by_cases hz : z ∈ e.target
    · simp only [Pi.add_apply, greenInverseChart_apply C _ hz]
      have hEq (y : M) : chartTest e ((f + h : 𝓓_{K}(X n, ℝ)) : X n → ℝ) y =
          chartTest e f y + chartTest e h y := by
        by_cases hy : y ∈ e.source <;> simp [chartTest, hy]
      rw [show (fun y => G (y, e.symm z) * chartTest e (⇑(f + h)) y) =
          fun y => G (y, e.symm z) * chartTest e f y + G (y, e.symm z) * chartTest e h y by
          funext y; rw [hEq, mul_add]]
      exact integral_add (integrable_greenInverseChart_kernel C hG hK f hz)
        (integrable_greenInverseChart_kernel C hG hK h hz)
    · simp [greenInverseChart, hz, e]
  map_smul' c f := by
    funext z
    let e := C.chart
    by_cases hz : z ∈ e.target
    · simp only [RingHom.id_apply, Pi.smul_apply, greenInverseChart_apply C _ hz, smul_eq_mul]
      have hEq (y : M) : chartTest e ((c • f : 𝓓_{K}(X n, ℝ)) : X n → ℝ) y = c * chartTest e f y := by
        by_cases hy : y ∈ e.source <;> simp [chartTest, hy, smul_eq_mul]
      rw [show (fun y => G (y, e.symm z) * chartTest e (⇑(c • f)) y) =
          fun y => c * (G (y, e.symm z) * chartTest e f y) by
          funext y; rw [hEq, mul_left_comm], integral_const_mul]
    · simp [greenInverseChart, hz, e]

@[simp]
theorem greenInverseChartLinear_apply (C : InteriorMetricChart J μ (nativeLaplace g))
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (hK : (K : Set (X n)) ⊆ C.chart.target) (f : 𝓓_{K}(X n, ℝ)) :
    greenInverseChartLinear C hG hK f = greenInverseChart C G f := by
  unfold greenInverseChartLinear
  rfl

omit [BorelSpace M] in
/-- The normalized weak inverse law gives the exact inverse identity for
the chart Laplacian on the compactly supported test domain. -/
theorem greenInverseChart_compactLaplace_eqOn (C : InteriorMetricChart J μ (nativeLaplace g))
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (hK : (K : Set (X n)) ⊆ C.chart.target) (f : 𝓓_{K}(X n, ℝ)) :
    EqOn (greenInverseChart C G (compactLaplace C.chart.open_target hK C.smooth_metric f))
      (fun z => -f z) C.chart.target := by
  intro z hz
  let e := C.chart
  let φ := chartTest e f
  have hSupp := f.tsupport_subset.trans hK
  have hφ := contMDiff_chartTest e C.smooth f.contDiff f.compact_supp hSupp
  have hφc := hasCompactSupport_chartTest e f.compact_supp hSupp
  have hφI : tsupport φ ⊆ (J).interior M := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := tsupport_chartTest_subset e f.compact_supp hSupp hy
    exact C.source_interior (e.map_target (hSupp hx))
  have hInv := (hG.weak_inverse _ (C.source_interior (e.map_target hz)) φ hφ hφc hφI).2
  have hp : φ (e.symm z) = f z := chartTest_comp_inverse e f hz
  rw [greenInverseChart_apply C _ hz, ← nativeLaplace_chartTest_laplace C hK f]
  simp_rw [mul_neg, integral_neg] at hInv
  exact neg_eq_iff_eq_neg.mp (hInv.trans hp)

omit [BorelSpace M] in
/-- Transposing the normalized inverse against a second-jet functional
gives its exact dual Laplace equation. The sign agrees with the inverse
of the negative Laplacian. -/
theorem greenInverseChart_secondJet_compactLaplace (C : InteriorMetricChart J μ (nativeLaplace g))
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (hK : (K : Set (X n)) ⊆ C.chart.target) (h0 : (0 : X n) ∈ C.chart.target)
    (hSmooth : ∀ f : 𝓓_{K}(X n, ℝ), ContDiffOn ℝ ∞ (greenInverseChart C G f) C.chart.target)
    (D : ScalarSecondJet n →ₗ[ℝ] ℝ) (f : 𝓓_{K}(X n, ℝ)) :
    -D (smoothSecondJet C.chart.open_target h0
        (greenInverseChart C G (compactLaplace C.chart.open_target hK C.smooth_metric f)) (hSmooth _)) =
      D (compactSecondJet f) := by
  have hnear := Filter.mem_of_superset (C.chart.open_target.mem_nhds h0)
    (greenInverseChart_compactLaplace_eqOn C hG hK f)
  have hNeg : ContDiffOn ℝ ∞ (fun z => -f z) C.chart.target := f.contDiff.contDiffOn.neg
  rw [smoothSecondJet_congr_germ C.chart.open_target C.chart.open_target h0 h0 (hSmooth _) hNeg hnear]
  let a : openChartScalars C.chart.target := ⟨f, f.contDiff.contDiffOn⟩
  have hJet : smoothSecondJet C.chart.open_target h0 (fun z => -f z) hNeg = -compactSecondJet f := by
    change smoothSecondJet C.chart.open_target h0 ((-a : openChartScalars C.chart.target) : X n → ℝ)
      (-a : openChartScalars C.chart.target).property = -compactSecondJet f
    rw [← openChartSecondJet_apply C.chart.open_target h0 (-a), map_neg, openChartSecondJet_apply]
    rfl
  rw [hJet, map_neg, neg_neg]

end CalderonPatch
