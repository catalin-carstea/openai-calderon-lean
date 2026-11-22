module

public import Proof.CalderonPatch.CapSourceSeparation
public import Proof.CalderonPatch.KernelJetTransposition

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Manifold Topology

namespace CalderonPatch

open CalderonN (X Harmonic InteriorMetricChart IsDirichletGreenKernel chartTest tsupport_chartTest_subset)

variable {n : ℕ} [NeZero n] {F M : Type*} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n

variable {g : SmoothMetric n M} {μ : Measure M} {G : M × M → ℝ} {K : Compacts (X n)}

/-- A transposed inverse with its smooth harmonic representative away
from the pole is supported at that pole once its cap pairings vanish. -/
theorem pointSupport_of_puncturedInverse (hn : 2 ≤ n) (hμ : IsMetricVolume g μ)
    (C : InteriorMetricChart J μ (nativeLaplace g)) (hK : (K : Set (X n)) ⊆ C.chart.target)
    (h0 : (0 : X n) ∈ C.chart.target) {E : M → F → ℝ} (Cap : CapSourceRepresentation E G)
    (W : 𝓓_{K}(X n, ℝ) →L[ℝ] ℝ) (w : M → ℝ)
    (hCont : ContinuousOn w ((J).interior M \ {C.chart.symm 0}))
    (hHarmonic : ∀ V : InteriorMetricChart J μ (nativeLaplace g),
      V.chart.source ⊆ (J).interior M \ {C.chart.symm 0} → Harmonic V.chart.target V.metric (w ∘ V.chart.symm))
    (hCap : ∀ φ : X n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Cap.domain ∩ Cap.chart.symm ⁻¹' ({C.chart.symm 0} : Set M)ᶜ →
      (∫ x in Cap.domain, φ x * w (Cap.chart.symm x) * Cap.density x) = 0)
    (hRep : ∀ f : 𝓓_{K}(X n, ℝ), tsupport (chartTest C.chart f) ⊆ (J).interior M \ {C.chart.symm 0} →
      W f = ∫ y, chartTest C.chart f y * w y ∂μ) :
    ∀ f : 𝓓_{K}(X n, ℝ), (f : X n → ℝ) =ᶠ[𝓝 0] 0 → W f = 0 := by
  have hZero : EqOn w 0 ((J).interior M \ {C.chart.symm 0}) := by
    apply eqOn_puncturedInterior_of_cap_tests hn g μ hμ Cap (finite_singleton _) hCont continuousOn_const
    · intro φ hφ hc hs
      change (∫ x in Cap.domain, φ x * w (Cap.chart.symm x) * Cap.density x) =
        ∫ x in Cap.domain, φ x * (0 : ℝ) * Cap.density x
      simpa using hCap φ hφ hc hs
    · intro V hV
      refine ⟨hHarmonic V hV, contDiffOn_const, fun z _ => ?_⟩
      have h (i : CalderonN.I n) : CalderonN.coordDeriv i (0 : X n → ℝ) = 0 := by
        funext x
        simp [CalderonN.coordDeriv, Pi.zero_def]
      change CalderonN.laplace V.metric 0 z = 0
      simp [CalderonN.laplace, h]
  intro f hf
  have hSupp : tsupport (f : X n → ℝ) ⊆ C.chart.target := f.tsupport_subset.trans hK
  have hNot : (0 : X n) ∉ tsupport (f : X n → ℝ) := notMem_tsupport_iff_eventuallyEq.mpr hf
  have hs : tsupport (chartTest C.chart f) ⊆ (J).interior M \ {C.chart.symm 0} := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := tsupport_chartTest_subset C.chart f.compact_supp hSupp hy
    refine ⟨C.source_interior (C.chart.map_target (hSupp hz)), fun h => ?_⟩
    have hz0 := C.chart.symm.injOn (hSupp hz) h0 (mem_singleton_iff.mp h)
    exact hNot (hz0 ▸ hz)
  rw [hRep f hs]
  have hEq : (fun y => chartTest C.chart f y * w y) = 0 := by
    funext y
    by_cases hy : y ∈ tsupport (chartTest C.chart f)
    · rw [hZero (hs hy), Pi.zero_apply, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, Pi.zero_apply]
  rw [hEq]
  exact integral_zero _ _

variable [AddCommGroup F] [Module ℝ F]

/-- At a point outside the cap sources, the actual Dirichlet inverse
gives the full harmonic jet range with its local regularity and
off-pole representation. -/
theorem range_sourceSecondJet_from_greenInverse (hn : 2 ≤ n) (hμ : IsMetricVolume g μ)
    (C : InteriorMetricChart J μ (nativeLaplace g)) (hK : (K : Set (X n)) ⊆ C.chart.target)
    (hK0 : (K : Set (X n)) ∈ 𝓝 0) (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    {E : M → F → ℝ} (Cap : CapSourceRepresentation E G)
    (u : F →ₗ[ℝ] (X n → ℝ)) (hu : ∀ f, Harmonic C.chart.target C.metric (u f))
    (hSmooth : ∀ f : 𝓓_{K}(X n, ℝ), ContDiffOn ℝ ∞ (greenInverseChart C G f) C.chart.target)
    (hAnalytic : ∀ D : ScalarSecondJet n →ₗ[ℝ] ℝ,
      let h0 := hK (mem_of_mem_nhds hK0)
      let A := sourceSecondJet C.chart.open_target h0 u (fun f => (hu f).1)
      let T := fun f : 𝓓_{K}(X n, ℝ) =>
        -D (smoothSecondJet C.chart.open_target h0 (greenInverseChart C G f) (hSmooth f))
      (∀ f, D (A f) = 0) → Continuous T ∧ ∃ w : M → ℝ,
        ContinuousOn w ((J).interior M \ {C.chart.symm 0}) ∧
        (∀ V : InteriorMetricChart J μ (nativeLaplace g),
          V.chart.source ⊆ (J).interior M \ {C.chart.symm 0} →
          Harmonic V.chart.target V.metric (w ∘ V.chart.symm)) ∧
        (∀ φ : X n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ Cap.domain ∩ Cap.chart.symm ⁻¹' ({C.chart.symm 0} : Set M)ᶜ →
          ∃ b : F, (∫ x in Cap.domain, φ x * w (Cap.chart.symm x) * Cap.density x) = -D (A b)) ∧
        ∀ f : 𝓓_{K}(X n, ℝ), tsupport (chartTest C.chart f) ⊆ (J).interior M \ {C.chart.symm 0} →
          T f = ∫ y, chartTest C.chart f y * w y ∂μ) :
    let h0 := hK (mem_of_mem_nhds hK0)
    (sourceSecondJet C.chart.open_target h0 u (fun f => (hu f).1)).range =
      (laplaceOnSecondJet C.metric 0).ker := by
  intro h0
  let A := sourceSecondJet C.chart.open_target h0 u (fun f => (hu f).1)
  have hH (f : F) : laplaceOnSecondJet C.metric 0 (A f) = 0 := by
    rw [show A f = _ from sourceSecondJet_apply C.chart.open_target h0 u (fun f => (hu f).1) f,
      smoothSecondJet_laplace]
    exact (hu f).2 0 h0
  apply range_sourceSecondJet_of_pointSupported_inverses C.chart.open_target hK hK0 C.smooth_metric A hH
  intro D hD
  obtain ⟨hCont, w, hw, hHarm, hCap, hRep⟩ := hAnalytic D hD
  have hS (f : 𝓓_{K}(X n, ℝ)) : ContDiffOn ℝ ∞ (greenInverseChartLinear C hG hK f) C.chart.target := by
    simpa only [greenInverseChartLinear_apply] using hSmooth f
  let B := sourceSecondJet C.chart.open_target h0 (greenInverseChartLinear C hG hK) hS
  have hApp (f : 𝓓_{K}(X n, ℝ)) : B f =
      smoothSecondJet C.chart.open_target h0 (greenInverseChart C G f) (hSmooth f) := by
    rw [show B f = _ from sourceSecondJet_apply C.chart.open_target h0 (greenInverseChartLinear C hG hK) hS f]
    exact smoothSecondJet_congr_germ C.chart.open_target C.chart.open_target h0 h0 (hS f) (hSmooth f)
      (Filter.EventuallyEq.of_eq (greenInverseChartLinear_apply C hG hK f))
  let W : 𝓓_{K}(X n, ℝ) →L[ℝ] ℝ :=
    ⟨-(D.comp B), by
      change Continuous (fun f => -D (B f))
      simpa only [hApp] using hCont⟩
  refine ⟨W, ?_, ?_⟩
  · apply pointSupport_of_puncturedInverse hn hμ C hK h0 Cap W w hw hHarm
    · intro φ hφ hc hs
      obtain ⟨b, hb⟩ := hCap φ hφ hc hs
      rw [hb, hD b, neg_zero]
    · intro f hf
      change -D (B f) = _
      rw [hApp]
      exact hRep f hf
  · intro f
    change -D (B (compactLaplace C.chart.open_target hK C.smooth_metric f)) = D (compactSecondJet f)
    rw [hApp]
    exact greenInverseChart_secondJet_compactLaplace C hG hK h0 hSmooth D f

end CalderonPatch
