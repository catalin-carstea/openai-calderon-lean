module

public import Proof.CalderonPatch.NativeCapSourceJets
public import Proof.CalderonPatch.NativeInverseRegularityProof

import Proof.CalderonPatch.NativeCapGreenKernel
import Proof.CalderonN.GreenRestriction
import Mathlib.Tactic

public section

open Filter Metric Set TopologicalSpace
open scoped ContDiff Distributions Manifold Topology
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
              A.smooth_inverse).contDiffOn)) = (laplaceOnSecondJet A.metric 0).ker) := by
  let rD := nativeInverseRegularity D
  obtain ⟨G,hG,hRep⟩ := exists_nativeCapGreenKernel D rD
  obtain ⟨p,hp⟩ := hUne
  obtain ⟨e,hpe,heU,heI,he,hes⟩ :=
    exists_interiorChart p (hUInt (subset_closure hp)) hU hp
  let A := nativeInteriorMetricChart D.metric D.volume D.metric_volume e heI he hes
  let z := e p
  obtain ⟨s,hs,hBall⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hpe))
  let K : Compacts (X (m+1)) := ⟨closedBall z (s/2), isCompact_closedBall z (s/2)⟩
  let V := ball z (s/2)
  have hKV : V ⊆ (K : Set _) := ball_subset_closedBall
  have hK : (K : Set _) ⊆ A.chart.target :=
    (closedBall_subset_ball (half_lt_self hs)).trans hBall
  have hV : IsOpen V := isOpen_ball
  have hVc : IsConnected V := (convex_ball z (s/2)).isConnected ⟨z, mem_ball_self (half_pos hs)⟩
  have hImage : A.chart.symm '' (K : Set _) ⊆ U := by
    rintro _ ⟨x,hx,rfl⟩
    exact heU (e.map_target (hK hx))
  have hsupp (f : 𝓓_{K}(X (m+1), ℝ)) :
      tsupport (smoothChartSource A hK f : M → ℝ) ⊆ U := by
    change tsupport (CalderonN.chartTest A.chart f) ⊆ U
    exact (CalderonN.tsupport_chartTest_subset A.chart f.compact_supp
      (f.tsupport_subset.trans hK)).trans ((image_mono f.tsupport_subset).trans hImage)
  let Q := nativeCapSourceRepresentation rD A hK hV hVc hKV hG hRep
  let EV := sourceEvaluations_of_capSolutions hn D.metric_volume Q hG
    (continuous_pi fun f => (nativeCapSolution_smooth rD A hK f).continuous)
    (fun _ hx => funext fun f => nativeCapSolution_zero_trace rD A hK f hx)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f _
    exact ⟨(D.smoothInverse_spec rD f).1.continuous, (D.smoothInverse_spec rD f).2.1⟩
  · intro x hx
    by_contra! h
    apply EV.interior_ne_zero x hx
    funext f
    exact h (smoothChartSource A hK f) (hsupp f)
  · intro x hx y hy hxy
    by_contra! h
    apply hxy (EV.separates hx hy ?_)
    funext f
    exact h (smoothChartSource A hK f) (hsupp f)
  · intro B hB h0
    have hB' : B.chart.source ⊆ (J m).interior M \ A.chart.symm '' (K : Set _) :=
      fun x hx => ⟨(hB hx).1, fun hs => (hB hx).2 (subset_closure (hImage hs))⟩
    have hRange := nativeCapCenteredSecondJetRange rD A hK hV hVc hKV hG hRep hn B hB' h0
    apply Subset.antisymm
    · rintro v ⟨f,rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, smoothSecondJet_laplace]
      have hS := D.smoothInverse_spec rD f.val
      let x := B.chart.symm 0
      have hxB : x ∈ B.chart.source := B.chart.map_target h0
      have hxI : x ∈ (J m).interior M := (hB hxB).1
      have hx0 : f.val x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => (hB hxB).2 (subset_closure (f.property h)))
      have hu := hS.2.2.1 hxI
      have hEucl := B.laplace_eq _ hS.1 x hxB
      rw [show B.chart x = 0 from B.chart.right_inv h0] at hEucl
      exact hEucl.symm.trans (neg_eq_zero.mp (hu.trans hx0))
    · intro v hv
      change v ∈ (laplaceOnSecondJet B.metric 0).ker at hv
      rw [← hRange] at hv
      obtain ⟨f,hf⟩ := hv
      rw [sourceSecondJet_apply] at hf
      change smoothSecondJet B.chart.open_target h0
        (nativeCapSolutionLinear rD A hK f ∘ B.chart.symm) _ = v at hf
      let F := smoothChartSource A hK f
      have hF := ((D.smoothInverse_spec rD F).1.comp_contMDiffOn B.smooth_inverse).contDiffOn
      have hEq : D.smoothInverse rD F ∘ B.chart.symm =ᶠ[𝓝 (0 : X (m+1))]
          nativeCapSolutionLinear rD A hK f ∘ B.chart.symm :=
        Filter.Eventually.of_forall (fun x => congrFun (nativeCapSolutionLinear_apply rD A hK f).symm
          (B.chart.symm x))
      refine ⟨⟨F, hsupp f⟩, ?_⟩
      exact (smoothSecondJet_congr_germ B.chart.open_target B.chart.open_target h0 h0
        hF (nativeCapChartSolution_harmonic rD A hK B hB' f).1 hEq).trans hf


end CalderonPaper
