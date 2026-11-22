module

public import Proof.CalderonPatch.GreenInverseChartRegularity
public import Proof.CalderonPatch.CapSourceSeparation

import Proof.CalderonN.MetricCalculus

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Manifold Topology

namespace CalderonPatch

open CalderonN (X InteriorMetricChart IsDirichletGreenKernel chartTest chartVolume)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ, ℝ)
local notation "Y" => X (m+1)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)
variable (C : InteriorMetricChart (𝓡∂ (m+1)) D.volume (nativeLaplace D.metric))
variable {K : Compacts (X (m+1))} (hK : (K : Set (X (m+1))) ⊆ C.chart.target)

/-- The actual native Green representation on all smooth sources. -/
abbrev RepresentsNativeInverse (G : M × M → ℝ) : Prop :=
  ∀ q ∈ (J).interior M, ∀ f : Source,
    Integrable (fun p => G (p,q) * f p) D.volume ∧
    (∫ p, G (p,q) * f p ∂D.volume) = D.smoothInverse h f q

/-- The source assigned to a label is the original chart test extended by zero. -/
@[expose] def nativeChartSourceLinear : 𝓓_{K}(Y, ℝ) →ₗ[ℝ] Source where
  toFun f := chartTestSource C f f.contDiff f.compact_supp (f.tsupport_subset.trans hK)
  map_add' f g := by
    apply Subtype.ext
    funext p
    change chartTest C.chart (⇑(f+g)) p = chartTest C.chart f p + chartTest C.chart g p
    by_cases hp : p ∈ C.chart.source <;> simp [chartTest, hp]
  map_smul' a f := by
    apply Subtype.ext
    funext p
    change chartTest C.chart (⇑(a • f)) p = a * chartTest C.chart f p
    by_cases hp : p ∈ C.chart.source <;> simp [chartTest, hp, smul_eq_mul]

omit [CompactSpace M] [BorelSpace M] [PreconnectedSpace M] in
@[simp]
theorem nativeChartSourceLinear_apply (f : 𝓓_{K}(Y, ℝ)) :
    nativeChartSourceLinear C hK f = smoothChartSource C hK f := rfl

/-- The common source labels are interpreted using the same canonical weak inverse
that is represented by the native Green kernel. -/
@[expose] def nativeCapSolutionLinear : 𝓓_{K}(Y, ℝ) →ₗ[ℝ] (M → ℝ) :=
  (D.smoothInverseL h).comp (nativeChartSourceLinear C hK)

theorem nativeCapSolutionLinear_apply (f : 𝓓_{K}(Y, ℝ)) :
    nativeCapSolutionLinear h C hK f = D.smoothInverse h (smoothChartSource C hK f) := rfl

theorem nativeCapSolution_smooth (f : 𝓓_{K}(Y, ℝ)) :
    ContMDiff J R ∞ (nativeCapSolutionLinear h C hK f) :=
  (D.smoothInverse_spec h (smoothChartSource C hK f)).1

theorem nativeCapSolution_zero_trace (f : 𝓓_{K}(Y, ℝ)) :
    EqOn (nativeCapSolutionLinear h C hK f) 0 ((J).boundary M) :=
  (D.smoothInverse_spec h (smoothChartSource C hK f)).2.1

omit [CompactSpace M] [BorelSpace M] [PreconnectedSpace M] in
/-- A coordinate forcing vanishes off the native image of its support set. -/
theorem smoothChartSource_eq_zero_off (f : 𝓓_{K}(Y, ℝ)) {p : M}
    (hp : p ∉ C.chart.symm '' (K : Set Y)) : smoothChartSource C hK f p = 0 := by
  change chartTest C.chart f p = 0
  by_cases hS : p ∈ C.chart.source
  · have hKp : C.chart p ∉ (K : Set Y) := fun hx => hp ⟨_, hx, C.chart.left_inv hS⟩
    rw [chartTest, indicator_of_mem hS, Function.comp_apply]
    exact f.zero_on_compl hKp
  · rw [chartTest, indicator_of_notMem hS]

/-- Every label is supported over the one fixed compact set, so its solution
is harmonic in the interior outside the image of that set. -/
theorem nativeCapSolution_harmonic_off (f : 𝓓_{K}(Y, ℝ)) :
    EqOn (nativeLaplace D.metric (nativeCapSolutionLinear h C hK f)) 0
      ((J).interior M \ C.chart.symm '' (K : Set Y)) := by
  intro p hp
  have hR := (D.smoothInverse_spec h (smoothChartSource C hK f)).2.2.1 hp.1
  exact neg_eq_zero.mp (hR.trans (smoothChartSource_eq_zero_off C hK f hp.2))

/-- The supported source representation on either side follows from the
actual Green inverse and the chart volume identity. -/
@[expose] def nativeCapSourceRepresentation {V : Set Y} (hV : IsOpen V) (hVc : IsConnected V)
    (hVK : V ⊆ (K : Set Y)) {G : M × M → ℝ}
    (hG : IsDirichletGreenKernel J D.volume (nativeLaplace D.metric) G)
    (hRep : RepresentsNativeInverse h G) :
    CapSourceRepresentation (n := m+1) (fun p f => nativeCapSolutionLinear h C hK f p) G where
  chart := C.chart
  domain := V
  open_domain := hV
  connected_domain := hVc
  domain_subset := hVK.trans hK
  interior := fun x hx => C.source_interior (C.chart.map_target (hK (hVK hx)))
  density := chartVolume C.metric
  density_continuous := (CalderonN.contDiffOn_metric_volume C.smooth_metric).continuousOn.mono (hVK.trans hK)
  density_positive := fun x hx => Real.sqrt_pos.mpr (C.smooth_metric.2 x (hK (hVK hx))).det_pos
  representation φ hφ hc hSupp := by
    let f : 𝓓_{K}(Y, ℝ) := ⟨φ, hφ, fun _ hx =>
      image_eq_zero_of_notMem_tsupport (fun hs => hx (hVK (hSupp hs)))⟩
    refine ⟨f, fun q hq => ?_⟩
    rw [nativeCapSolutionLinear_apply]
    exact smoothInverse_chartTestSource_eq_greenIntegral h C hG hRep (hVK.trans hK) hφ hc hSupp hq

end CalderonPatch
