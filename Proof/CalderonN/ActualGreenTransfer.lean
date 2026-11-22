module

public import Proof.CalderonN.ActualMovingTraceAdjoint
public import Proof.CalderonN.MovingGreenFluxDensity
public import Proof.CalderonN.GreenTraceEquation
public import Proof.CalderonN.ActualEnlargedNormalTrace

import Proof.CalderonN.MetricBallDirichlet
import Proof.CalderonN.CrossProductWeak
import Mathlib.Tactic

/-! Adapted from `ActualGreenTransfer` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 2300000 in
/-- The actual continued kernel supplies the normalized conormal density
and the literal adjoint. Its uncut density solves the homogeneous
moving trace equation on every fiber. -/
theorem actualGreenTransfer
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {γ g₁ g₂ : (MetricField dim)}
    (hγ : SmoothMetric univ γ) (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hNormal : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hFrame : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) (hR : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O) {G : (X dim) × (X dim) → ℝ}
    (hG : ProductSolutionOn g₁ g₂ O G)
    (hSphere : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim), (E (y,r y • frameVector e y w),y) ∈ O) :
    let A := actualMovingTraceAdjoint γ g₁ E e r
    let ψ := movingGreenFluxDensity γ g₁ E e r G
    Dirichlet Y γ g₁ E r ∧ IsMovingTraceAdjoint Y γ g₁ e E r A ∧
      smoothNear ψ (bundle Y γ) ∧
      (∀ y ∈ Y, ∀ u, HarmonicOnBall g₁ (closedBallImage γ E r y) u →
        (∫ w : ↥(standardSphere dim), ψ (y,frameVector e y w) *
          u (endpoint E r (y,frameVector e y w)) ∂(sphereProbability dim)) =
          normalSphereGreenFlux g₁ E e r G y u) ∧
      ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
        movingTrace γ g₂ r A (fun q => (ψ q : ℂ)) (y,frameVector e y w) = 0 := by
  let A := actualMovingTraceAdjoint γ g₁ E e r
  let ψ := movingGreenFluxDensity γ g₁ E e r G
  have h₁Ω := smoothMetric_restrict hg₁ (subset_univ Ω)
  have hDir := normalDirichlet_of_metric hΩ h₁Ω hE hNormal hFrame hR
  have hAdj := isMovingTraceAdjoint_actual hΩ hγ hg₁ hE hNormal he hFrame hr hR
  obtain ⟨U,hU,hCU,_,hm,hPos,_⟩ := exists_smooth_movingBallFamilies hγ hg₁ hE hNormal he hFrame hr hR
  let Q (q : (X dim) × (X dim)) := (normalBallChartMap E e q.1 (r q.1) q.2,q.1)
  let T := Q ⁻¹' O
  have hQ : ContDiff ℝ ∞ Q := (contDiff_movingNormalEndpoint hE he hr).prodMk contDiff_fst
  have hT : IsOpen T := hO.preimage hQ.continuous
  have hST : Y ×ˢ (standardSphere dim) ⊆ T := fun q hq => hSphere q.1 hq.1 ⟨q.2,hq.2⟩
  have hGS : ContDiffOn ℝ ∞ (framedMovingGreenKernel E e r G) T :=
    hG.1.comp hQ.contDiffOn (fun _ hq => hq)
  have hψ : smoothNear ψ (bundle Y γ) :=
    smoothNear_movingGreenFluxDensity hγ he hFrame hr hU hT hCU hST hm hPos hGS
  have hFlux (y : (X dim)) (hy : y ∈ Y) (u : (X dim) → ℝ)
      (hu : HarmonicOnBall g₁ (closedBallImage γ E r y) u) :
      (∫ w : ↥(standardSphere dim), ψ (y,frameVector e y w) *
        u (endpoint E r (y,frameVector e y w)) ∂(sphereProbability dim)) =
        normalSphereGreenFlux g₁ E e r G y u := by
    have hp : ContDiff ℝ ∞ (Prod.mk y : (X dim) → (X dim) × (X dim)) := contDiff_const.prodMk contDiff_id
    have hU' := hU.preimage hp.continuous
    have hCU' : closedBall (0 : (X dim)) 1 ⊆ (Prod.mk y) ⁻¹' U := fun _ hz => hCU ⟨hy,hz⟩
    have hG' : smoothNear (fun z => framedMovingGreenKernel E e r G (y,z)) (standardSphere dim) :=
      ⟨(Prod.mk y) ⁻¹' T,hT.preimage hp.continuous,fun _ hz => hST ⟨hy,hz⟩,
        hGS.comp hp.contDiffOn (fun _ hz => hz)⟩
    exact movingGreenFluxDensity_represents hΩ h₁Ω hE hNormal hy (hFrame y hy) (hR y hy).1 (hR y hy).2
      hU' hCU' (smoothMetric_movingBall_slice hm hPos y) hG' hu
  refine ⟨hDir,hAdj,hψ,hFlux,?_⟩
  intro y hy
  have hψℂ : smoothNear (fun q => (ψ q : ℂ)) (bundle Y γ) := by
    obtain ⟨S,hS,hBS,hψS⟩ := hψ
    exact ⟨S,hS,hBS,Complex.ofRealCLM.contDiff.comp_contDiffOn hψS⟩
  have hP : smoothNear (movingTrace γ g₂ r A (fun q => (ψ q : ℂ))) (bundle Y γ) :=
    smoothNear_movingTrace hY (smoothMetric_restrict hγ (subset_univ Y))
      (smoothMetric_restrict hg₂ (subset_univ Y)) hr.contDiffOn hAdj hψℂ
  apply field_eq_zero_of_neighborhood_trace_pairings hy (hFrame y hy) hP
  · intro V hV hCover u hu
    exact sphereTracePair_movingTrace_of_greenFlux hY hγ hg₁ hE hNormal hO hG hFrame
      (fun i => (he i).contDiffOn) hr.contDiffOn hR hSphere hAdj hψ hFlux hy hV hCover hu
  · intro a ha
    exact exists_enlarged_normalTrace_family hg₁ hE hNormal hy (hFrame y hy) (hR y hy).1 (hR y hy).2 ha

end CalderonN
