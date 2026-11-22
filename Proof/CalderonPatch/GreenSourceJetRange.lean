module

public import Proof.CalderonPatch.GreenJetOnTests
public import Proof.CalderonPatch.GreenInverseJetContinuity
public import Proof.CalderonPatch.PuncturedJetContinuation

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Manifold Topology Matrix.Norms.Elementwise

namespace CalderonPatch

open CalderonN (I X Harmonic InteriorMetricChart IsDirichletGreenKernel parameterSecondOrder chartTest)

variable {n : ℕ} [NeZero n] {F M : Type*} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n

/-- The differentiated kernel supplies the off-pole representative
of a transposed jet. The additional analytic inputs concern the
regularity of the inverse on all tests and continuity of jet evaluation. -/
theorem range_sourceSecondJet_of_greenKernel
    [AddCommGroup F] [Module ℝ F]
    {g : SmoothMetric n M} {μ : Measure M} {G : M × M → ℝ} {K : Compacts (X n)}
    (hn : 2 ≤ n) (hμ : IsMetricVolume g μ)
    (C S : InteriorMetricChart J μ (nativeLaplace g))
    (hK : (K : Set (X n)) ⊆ C.chart.target) (hK0 : (K : Set (X n)) ∈ 𝓝 0)
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    {E : M → F → ℝ} (Cap : CapSourceRepresentation E G)
    (hCapChart : Cap.chart = S.chart)
    (hCapDensity : ContDiffOn ℝ ∞ Cap.density Cap.domain)
    (u : F →ₗ[ℝ] (X n → ℝ)) (hu : ∀ f, Harmonic C.chart.target C.metric (u f))
    (hEval : ∀ f z, z ∈ C.chart.target → u f z = E (C.chart.symm z) f)
    (hSmooth : ∀ f : 𝓓_{K}(X n, ℝ), ContDiffOn ℝ ∞ (greenInverseChart C G f) C.chart.target)
    (hBound : ∃ (orders : Finset ℕ) (B : ℝ), 0 ≤ B ∧
      ∀ f : 𝓓_{K}(X n, ℝ),
        ‖smoothSecondJet C.chart.open_target (hK (mem_of_mem_nhds hK0))
          (greenInverseChart C G f) (hSmooth f)‖ ≤ B * (orders.sup fun i => N[ℝ]_{K, i}) f) :
    let h0 := hK (mem_of_mem_nhds hK0)
    (sourceSecondJet C.chart.open_target h0 u (fun f => (hu f).1)).range =
      (laplaceOnSecondJet C.metric 0).ker := by
  intro h0
  apply range_sourceSecondJet_from_greenInverse hn hμ C hK hK0 hG Cap u hu hSmooth
  intro D
  dsimp only
  intro hAnnihilates
  obtain ⟨a,b,c,hD⟩ := exists_parameterSecondOrder_for_jetFunctional (-D)
  let p := C.chart.symm 0
  let w : M → ℝ := fun y => parameterSecondOrder a b c (fun s => G (y,C.chart.symm s)) 0
  let U := (J).interior M \ {p}
  have hU : IsOpen U := ((J).isOpen_interior (n := ∞) (by simp)).sdiff isClosed_singleton
  have hH (A : InteriorMetricChart J μ (nativeLaplace g)) (hA : A.chart.source ⊆ U) :
      Harmonic A.chart.target A.metric (w ∘ A.chart.symm) :=
    harmonic_greenParameterJet_off_pole hG C A h0
      (fun h => (hA h).2 (mem_singleton p)) a b c
  have hW : ContinuousOn w U := by
    intro x hx
    obtain ⟨e,hxe,heU,heI,he,hes⟩ := exists_interiorChart x hx.1 hU hx
    let A := nativeInteriorMetricChart g μ hμ e heI he hes
    have hA := hH A heU
    have hCom : ContinuousOn ((w ∘ e.symm) ∘ e) e.source :=
      hA.1.continuousOn.comp e.continuousOn (fun _ hx => e.map_source hx)
    have heq : w =ᶠ[𝓝 x] (w ∘ e.symm) ∘ e :=
      Filter.mem_of_superset (e.open_source.mem_nhds hxe) (fun y hy => by
        change w y = w (e.symm (e y))
        rw [e.left_inv hy])
    exact ((hCom.continuousAt (e.open_source.mem_nhds hxe)).congr_of_eventuallyEq heq).continuousWithinAt
  refine ⟨continuous_greenInverseSecondJet_of_testBound C hG hK h0 hSmooth hBound D,
    w,hW,hH,?_,?_⟩
  · intro φ hφ hc hs
    obtain ⟨d,hd⟩ := Cap.representation φ hφ hc (hs.trans inter_subset_left)
    let W := fun x => φ x * Cap.density x
    have hSCap : Cap.domain ⊆ S.chart.target := hCapChart ▸ Cap.domain_subset
    have hApart : C.chart.symm 0 ∉ S.chart.symm '' tsupport φ := by
      rintro ⟨x,hx,hxp⟩
      have h := (hs hx).2
      change Cap.chart.symm x ∉ ({p} : Set M) at h
      rw [hCapChart, hxp] at h
      exact h (mem_singleton p)
    have hP := greenParameterSecondOrder_pairing hG S C Cap.open_domain hSCap hc
      (hs.trans inter_subset_left) h0 hApart W
      (hφ.contDiffOn.mul hCapDensity)
      (fun x hx => mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hx.2) _) a b c
    have hNear : u d =ᶠ[𝓝 (0 : X n)]
        fun z => ∫ x in Cap.domain, W x * G (S.chart.symm x,C.chart.symm z) := by
      filter_upwards [C.chart.open_target.mem_nhds h0] with z hz
      rw [hEval d z hz, hd _ (C.source_interior (C.chart.map_target hz))]
      apply setIntegral_congr_fun Cap.open_domain.measurableSet
      intro x _
      rw [hCapChart]
      change φ x * G (S.chart.symm x,C.chart.symm z) * Cap.density x = _
      exact mul_right_comm _ _ _
    refine ⟨d,?_⟩
    calc
      _ = ∫ x in Cap.domain, W x * parameterSecondOrder a b c
          (fun s => G (S.chart.symm x,C.chart.symm s)) 0 := by
        apply setIntegral_congr_fun Cap.open_domain.measurableSet
        intro x _
        rw [hCapChart]
        change φ x * w (S.chart.symm x) * Cap.density x = W x * w (S.chart.symm x)
        exact mul_right_comm _ _ _
      _ = parameterSecondOrder a b c (u d) 0 := hP.symm.trans
        (parameterSecondOrder_congr_germ a b c hNear).symm
      _ = _ := by
        rw [← hD C.chart.open_target h0 (u d) (hu d).1, LinearMap.neg_apply, sourceSecondJet_apply]
  · intro f hf
    have hPole : C.chart.symm 0 ∉ tsupport (chartTest C.chart f) :=
      fun hp => (hf hp).2 (mem_singleton p)
    have hF : (f : X n → ℝ) =ᶠ[𝓝 (0 : X n)] 0 := by
      have he := (notMem_tsupport_iff_eventuallyEq.mp hPole).comp_tendsto
        (C.chart.continuousAt_symm h0).tendsto
      filter_upwards [he,C.chart.open_target.mem_nhds h0] with z hz hz'
      exact (chartTest_comp_inverse C.chart f hz').symm.trans hz
    have h0ne := notMem_tsupport_iff_eventuallyEq.mpr hF
    calc
      _ = parameterSecondOrder a b c (greenInverseChart C G f) 0 :=
        hD C.chart.open_target h0 (greenInverseChart C G f) (hSmooth f)
      _ = _ := greenInverseChart_parameterSecondOrder_off_pole C hG hK h0 f h0ne a b c

end CalderonPatch
