module

public import Proof.CalderonPatch.GreenInverseChartRegularity
public import Proof.CalderonPatch.PointwiseSmoothFamilyJets

import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Manifold Matrix.Norms.Elementwise Topology

namespace CalderonPatch

open CalderonN (X InteriorMetricChart IsDirichletGreenKernel chartTest)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "Y" => X (m+1)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)
variable (C : InteriorMetricChart (𝓡∂ (m+1)) D.volume (nativeLaplace D.metric))
variable {K : Compacts (X (m+1))} (hK : (K : Set (X (m+1))) ⊆ C.chart.target)
variable {G : M × M → ℝ} (hG : IsDirichletGreenKernel (𝓡∂ (m+1)) D.volume (nativeLaplace D.metric) G)
variable (hRep : ∀ q ∈ (𝓡∂ (m+1)).interior M, ∀ f : smoothSourceSubmodule (m := m) (M := M),
    Integrable (fun p => G (p,q) * f p) D.volume ∧
    (∫ p, G (p,q) * f p ∂D.volume) = D.smoothInverse h f q)

include hK hG in
/-- Integration against an integrable column is continuous for the
order-zero seminorm of any fixed-support coordinate source. -/
private theorem exists_greenInverseChartEvaluation {z : Y} (hz : z ∈ C.chart.target) :
    ∃ L : 𝓓_{K}(Y, ℝ) →L[ℝ] ℝ, ∀ f, L f = greenInverseChart C G f z := by
  let q := C.chart.symm z
  have hq : q ∈ (J).interior M := C.source_interior (C.chart.map_target hz)
  let L := (LinearMap.proj z).comp (greenInverseChartLinear C hG hK)
  have hL (f : 𝓓_{K}(Y, ℝ)) : L f = greenInverseChart C G f z := by
    change greenInverseChartLinear C hG hK f z = _
    rw [greenInverseChartLinear_apply]
  let B := ∫ p, ‖G (p,q)‖ ∂D.volume
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have hNorm (f : 𝓓_{K}(Y, ℝ)) : ‖L f‖ ≤ B * N[ℝ]_{K, 0} f := by
    rw [hL,greenInverseChart_apply C (G := G) f hz]
    change ‖∫ p, G (p,q) * chartTest C.chart f p ∂D.volume‖ ≤ B * N[ℝ]_{K, 0} f
    rw [mul_comm B,← integral_const_mul]
    apply norm_integral_le_of_norm_le ((hG.integrable _ hq).norm.const_mul _)
    filter_upwards with p
    rw [norm_mul,mul_comm (N[ℝ]_{K, 0} f)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    by_cases hp : p ∈ C.chart.source
    · rw [chartTest,indicator_of_mem hp,Function.comp_apply]
      exact ContDiffMapSupportedIn.norm_apply_le_seminorm ℝ
    · rw [chartTest,indicator_of_notMem hp,norm_zero]
      exact apply_nonneg _ _
  have hCont := WithSeminorms.continuous_normedSpace_rng ℝ
    (ContDiffMapSupportedIn.withSeminorms ℝ Y ℝ ⊤ K) L
    ⟨{0},⟨B,hB⟩,fun f => by
      rw [Finset.sup_singleton]
      change ‖L f‖ ≤ B * N[ℝ]_{K, 0} f
      exact hNorm f⟩
  exact ⟨⟨L,hCont⟩,hL⟩

include hG in
/-- The actual Green inverse obeys the finite-jet bound used in
transposition. Integrability of its columns and smoothness of its
solutions suffice for this argument by uniform boundedness. -/
theorem exists_greenInverseChart_secondJet_bound (h0 : (0 : Y) ∈ C.chart.target) :
    ∃ (orders : Finset ℕ) (B : ℝ), 0 ≤ B ∧ ∀ f : 𝓓_{K}(Y, ℝ),
      ‖smoothSecondJet C.chart.open_target h0 (greenInverseChart C G f)
        (contDiffOn_greenInverseChart_of_native h C hK hRep f)‖ ≤
        B * (orders.sup fun i => N[ℝ]_{K, i}) f :=
  exists_secondJetEvaluation_seminorm_bound C.chart.open_target (greenInverseChart C G)
    (contDiffOn_greenInverseChart_of_native h C hK hRep)
    (fun _ => exists_greenInverseChartEvaluation C hK hG) h0

end CalderonPatch
