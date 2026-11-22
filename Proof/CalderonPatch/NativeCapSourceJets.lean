module

public import Proof.CalderonPatch.NativeCapSourceFamily
public import Proof.CalderonPatch.GreenSourceJetRange
public import Proof.CalderonPatch.GreenKernelJetBound

import Proof.CalderonPatch.NativeChartRecenter
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Manifold Matrix.Norms.Elementwise Topology

namespace CalderonPatch

open CalderonN (X Mat Harmonic HarmonicCoordinates InteriorMetricChart IsDirichletGreenKernel
  chartVolume hessian laplace laplace_congrOn)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "Y" => X (m+1)
local notation "P" => 𝓘(ℝ, X (m+1))
local notation "R" => 𝓘(ℝ, ℝ)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)
variable (C : InteriorMetricChart (𝓡∂ (m+1)) D.volume (nativeLaplace D.metric))
variable {K : Compacts (X (m+1))} (hK : (K : Set (X (m+1))) ⊆ C.chart.target)

/-- Read the solutions from the given source labels in an interior target chart. -/
@[expose] def nativeCapChartSolution
    (A : InteriorMetricChart J D.volume (nativeLaplace D.metric)) :
    𝓓_{K}(Y, ℝ) →ₗ[ℝ] (Y → ℝ) where
  toFun f := nativeCapSolutionLinear h C hK f ∘ A.chart.symm
  map_add' f g := by rw [map_add]; rfl
  map_smul' a f := by rw [map_smul]; rfl

theorem nativeCapChartSolution_harmonic
    (A : InteriorMetricChart J D.volume (nativeLaplace D.metric))
    (hA : A.chart.source ⊆ (J).interior M \ C.chart.symm '' (K : Set Y))
    (f : 𝓓_{K}(Y, ℝ)) : Harmonic A.chart.target A.metric (nativeCapChartSolution h C hK A f) := by
  have hu := nativeCapSolution_smooth h C hK f
  refine ⟨(hu.comp_contMDiffOn A.smooth_inverse).contDiffOn, fun z hz => ?_⟩
  have hΔ := A.laplace_eq _ hu _ (A.chart.map_target hz)
  rw [A.chart.right_inv hz] at hΔ
  exact hΔ.symm.trans (nativeCapSolution_harmonic_off h C hK f (hA (A.chart.map_target hz)))

variable {V : Set (X (m+1))} (hV : IsOpen V) (hVc : IsConnected V) (hVK : V ⊆ (K : Set (X (m+1))))
variable {G : M × M → ℝ} (hG : IsDirichletGreenKernel (𝓡∂ (m+1)) D.volume (nativeLaplace D.metric) G)
variable (hRep : RepresentsNativeInverse h G)

include hV hVc hVK hG hRep in
/-- The exact kernel transposition theorem gives the full harmonic second jet
at the center of every chart outside the cap source region. -/
theorem nativeCapCenteredSecondJetRange (hn : 2 ≤ m+1)
    (A : InteriorMetricChart J D.volume (nativeLaplace D.metric))
    (hA : A.chart.source ⊆ (J).interior M \ C.chart.symm '' (K : Set Y))
    (h0 : (0 : Y) ∈ A.chart.target) :
    (sourceSecondJet A.chart.open_target h0 (nativeCapChartSolution h C hK A)
      (fun f => (nativeCapChartSolution_harmonic h C hK A hA f).1)).range =
        (laplaceOnSecondJet A.metric 0).ker := by
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (A.chart.open_target.mem_nhds h0)
  let K₀ : Compacts Y := ⟨closedBall 0 (r/2),isCompact_closedBall _ _⟩
  have hK₀ : (K₀ : Set Y) ⊆ A.chart.target := (closedBall_subset_ball (by linarith)).trans hBall
  have hKnear : (K₀ : Set Y) ∈ 𝓝 (0 : Y) := closedBall_mem_nhds _ (by positivity)
  let E := nativeCapSourceRepresentation h C hK hV hVc hVK hG hRep
  have hDensity : ContDiffOn ℝ ∞ E.density E.domain :=
    (CalderonN.contDiffOn_metric_volume C.smooth_metric).mono (hVK.trans hK)
  have hS := contDiffOn_greenInverseChart_of_native h A hK₀ hRep
  have hB := exists_greenInverseChart_secondJet_bound h A hK₀ hG hRep h0
  exact range_sourceSecondJet_of_greenKernel hn D.metric_volume A C hK₀ hKnear hG E rfl
    hDensity (nativeCapChartSolution h C hK A) (nativeCapChartSolution_harmonic h C hK A hA)
    (fun _ _ _ => rfl) hS hB

include hV hVc hVK hG hRep in
/-- Outside the cap support, the actual solutions realize every intrinsic covector. -/
theorem exists_nativeCapSolution_mfderiv (hn : 2 ≤ m+1) {p : M}
    (hp : p ∈ (J).interior M \ C.chart.symm '' (K : Set Y))
    (B : TangentSpace J p →L[ℝ] ℝ) :
    ∃ f, mfderiv J R (nativeCapSolutionLinear h C hK f) p = B := by
  let U := (J).interior M \ C.chart.symm '' (K : Set Y)
  have hImage : IsClosed (C.chart.symm '' (K : Set Y)) :=
    (K.isCompact.image_of_continuousOn (C.chart.continuousOn_symm.mono hK)).isClosed
  have hU : IsOpen U := ((J).isOpen_interior (n := ∞) (by simp)).sdiff hImage
  obtain ⟨e,hpe,heU,heI,he,hes⟩ := exists_interiorChart p hp.1 hU hp
  let c := e p
  let e₀ := recenterChart e c
  have he₀U : e₀.source ⊆ U := by rw [recenterChart_source]; exact heU
  have he₀ : ContMDiffOn J P ∞ e₀ e₀.source := recenterChart_smooth e he c
  have he₀s : ContMDiffOn P J ∞ e₀.symm e₀.target := recenterChart_smooth_inverse e hes c
  let A := nativeInteriorMetricChart D.metric D.volume D.metric_volume e₀
    (he₀U.trans sdiff_subset) he₀ he₀s
  have h0 : (0 : Y) ∈ e₀.target := recenterChart_zero_mem e (e.map_source hpe)
  have hpEq : e₀.symm 0 = p := by rw [recenterChart_symm_apply,add_zero,e.left_inv hpe]
  have hRange := nativeCapCenteredSecondJetRange h C hK hV hVc hVK hG hRep hn A he₀U h0
  let d : Y →L[ℝ] Y := mfderiv P J e₀.symm 0
  obtain ⟨f,hf⟩ := exists_source_fderiv_of_harmonicJetRange A.chart.open_target h0
    (A.smooth_metric.2 0 h0) (nativeCapChartSolution h C hK A)
    (fun f => (nativeCapChartSolution_harmonic h C hK A he₀U f).1) hRange (B.comp d)
  let u := nativeCapSolutionLinear h C hK f
  have hu := (nativeCapSolution_smooth h C hK f).mdifferentiableAt (x := e₀.symm 0) (by simp)
  have he₀D : e₀.MDifferentiable J P := ⟨he₀.mdifferentiableOn (by simp), he₀s.mdifferentiableOn (by simp)⟩
  have hD := mfderiv_comp (0 : Y) hu (he₀D.mdifferentiableAt_symm h0)
  rw [mfderiv_eq_fderiv] at hD
  have hCom : (mfderiv J R u (e₀.symm 0)).comp d = B.comp d := hD.symm.trans hf
  rw [hpEq] at hCom
  refine ⟨f,ContinuousLinearMap.ext fun v => ?_⟩
  obtain ⟨y,rfl⟩ := he₀D.symm.mfderiv_surjective h0 v
  exact DFunLike.congr_fun hCom y

include hV hVc hVK hG hRep in
/-- In any harmonic coordinates outside the cap support, the actual
native solutions span the exact trace-zero symmetric Hessian space. -/
theorem nativeCapSolution_hessianSpan (hn : 2 ≤ m+1)
    (e : OpenPartialHomeomorph M Y)
    (heU : e.source ⊆ (J).interior M \ C.chart.symm '' (K : Set Y))
    (he : ContMDiffOn J P ∞ e e.source) (hes : ContMDiffOn P J ∞ e.symm e.target)
    (heH : HarmonicCoordinates e.target (coordinateMetric D.metric e))
    {x : Y} (hx : x ∈ e.target) (S : Mat (m+1)) :
    S ∈ Submodule.span ℝ (range fun f => hessian (fun z => nativeCapSolutionLinear h C hK f (e.symm z)) x) ↔
      S.transpose = S ∧ ((coordinateMetric D.metric e x)⁻¹ * S).trace = 0 := by
  let e₀ := recenterChart e x
  have he₀U : e₀.source ⊆ (J).interior M \ C.chart.symm '' (K : Set Y) := by
    rw [recenterChart_source]
    exact heU
  let A := nativeInteriorMetricChart D.metric D.volume D.metric_volume e₀
    (he₀U.trans sdiff_subset) (recenterChart_smooth e he x) (recenterChart_smooth_inverse e hes x)
  have h0 : (0 : Y) ∈ e₀.target := recenterChart_zero_mem e hx
  have hMetric : EqOn A.metric (fun y => coordinateMetric D.metric e (x+y)) A.chart.target :=
    coordinateMetric_recenter e hes D.metric x
  have hH : HarmonicCoordinates A.chart.target A.metric := by
    intro i
    have hs := harmonicCoordinates_translate e.open_target heH x i
    refine ⟨?_, fun y hy => ?_⟩
    · change ContDiffOn ℝ ∞ (fun y : Y => y i) (recenterChart e x).target
      rw [recenterChart_target]
      exact hs.1
    have hy' : y ∈ (x + ·) ⁻¹' e.target := by
      change y ∈ e₀.target at hy
      rwa [recenterChart_target] at hy
    exact (laplace_congrOn A.chart.open_target hMetric (fun _ _ => rfl) hy).trans (hs.2 y hy')
  have hRange := nativeCapCenteredSecondJetRange h C hK hV hVc hVK hG hRep hn A he₀U h0
  have hJets := hessianSpan_of_harmonicJetRange A.chart.open_target h0 hH
    (nativeCapChartSolution h C hK A)
    (fun f => (nativeCapChartSolution_harmonic h C hK A he₀U f).1) hRange S
  have hGrad : (fun f => hessian (nativeCapChartSolution h C hK A f) 0) =
      fun f => hessian (fun y => nativeCapSolutionLinear h C hK f (e.symm y)) x := by
    funext f
    change hessian (fun y => nativeCapSolutionLinear h C hK f ((recenterChart e x).symm y)) 0 = _
    simp only [recenterChart_symm_apply]
    simpa only [add_zero] using hessian_translate x 0
      (fun y => nativeCapSolutionLinear h C hK f (e.symm y))
  have hMetricAt : A.metric 0 = coordinateMetric D.metric e x := by
    simpa only [add_zero] using hMetric h0
  rw [hGrad,hMetricAt] at hJets
  exact hJets

end CalderonPatch
