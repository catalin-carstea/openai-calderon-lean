module

public import Proof.CalderonN.LocalNormalGreenFlux
public import Proof.CalderonN.MovingTraceDuality
public import Proof.CalderonN.EnlargedTraceDensity

import Proof.CalderonN.CrossProductWeak
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Adapted from `GreenTraceEquation` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- A local density representing the actual sphere flux annihilates
the moving trace operator against any test harmonic on a neighborhood
of the closed normal ball. -/
theorem sphereTracePair_movingTrace_of_greenFlux
    {Y Ω : Set (X dim)} (hY : IsOpen Y)
    {γ g₁ g₂ : (MetricField dim)} (hγ : SmoothMetric univ γ) (hg₁ : SmoothMetric univ g₁)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O)
    {G : (X dim) × (X dim) → ℝ} (hG : ProductSolutionOn g₁ g₂ O G)
    {e : (Frame dim)} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Y) {r : (X dim) → ℝ}
    (hrc : ContDiffOn ℝ ∞ r Y) (hr : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    (hSphere : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim), (E (y,r y • frameVector e y w),y) ∈ O)
    {A : (TraceAdjoint dim)} (hA : IsMovingTraceAdjoint Y γ g₁ e E r A)
    {ψ : (X dim) × (X dim) → ℝ} (hψ : smoothNear ψ (bundle Y γ))
    (hFlux : ∀ y ∈ Y, ∀ u, HarmonicOnBall g₁ (closedBallImage γ E r y) u →
      (∫ w : ↥(standardSphere dim), ψ (y,frameVector e y w) *
        u (endpoint E r (y,frameVector e y w)) ∂(sphereProbability dim)) =
        normalSphereGreenFlux g₁ E e r G y u)
    {y₀ : (X dim)} (hy₀ : y₀ ∈ Y) {U : Set (X dim)} (hU : IsOpen U)
    (hCover : closedBallImage γ E r y₀ ⊆ U) {u : (X dim) → ℝ} (hu : Harmonic U g₁ u) :
    sphereTracePair e E r (movingTrace γ g₂ r A (fun q => (ψ q : ℂ))) u y₀ = 0 := by
  obtain ⟨V,hV,hyV,hVY,hB,hT⟩ := exists_harmonic_normalSphereGreenFlux_near hY hγ hg₁ hE hN
    hO hG he (fun i => (hec i).continuousOn) hrc.continuousOn hr hSphere hy₀ hU hCover hu
  have hv (y : (X dim)) (hy : y ∈ V) : HarmonicOnBall g₁ (closedBallImage γ E r y) u :=
    ⟨⟨U,hU,hB y hy,hu.1⟩,fun x hx => hu.2 x (hB y hy (interior_subset hx))⟩
  have hTrace := smoothNear_endpointTrace hV hU hE (hrc.mono hVY) hu.1 hB
  have hφ : smoothNear (fun q => (ψ q : ℂ)) (bundle Y γ) := by
    obtain ⟨W,hW,hsub,hs⟩ := hψ
    exact ⟨W,hW,hsub,Complex.ofRealCLM.contDiff.comp_contDiffOn hs⟩
  have hP : EqOn (sphereTracePair e E r (fun q => (ψ q : ℂ)) u)
      (fun y => (normalSphereGreenFlux g₁ E e r G y u : ℂ)) V := by
    intro y hy
    change (∫ w : ↥(standardSphere dim), (ψ (y,frameVector e y w) : ℂ) *
      (u (endpoint E r (y,frameVector e y w)) : ℂ) ∂(sphereProbability dim)) = _
    simp_rw [← Complex.ofReal_mul,integral_complex_ofReal,hFlux y (hVY hy) u (hv y hy)]
  exact sphereTracePair_movingTrace_eq_zero_of_harmonic hV hY hVY hγ
    (fun y hy => he y (hVY hy)) (fun i => (hec i).mono hVY) hA hφ hTrace hv hT hP hyV

/-- If harmonic traces from slightly larger balls approach the desired
boundary values, annihilation against neighborhood tests determines a
smooth field on the original sphere. -/
theorem field_eq_zero_of_neighborhood_trace_pairings
    {Y : Set (X dim)} {γ g : (MetricField dim)} {e : (Frame dim)} {E : (X dim) × (X dim) → (X dim)} {r : (X dim) → ℝ}
    {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field dim)} (hφ : smoothNear φ (bundle Y γ))
    (hAnn : ∀ {U : Set (X dim)}, IsOpen U → closedBallImage γ E r y ⊆ U →
      ∀ {u : (X dim) → ℝ}, Harmonic U g u → sphereTracePair e E r φ u y = 0)
    (hApprox : ∀ a : (X dim) → ℝ, smoothNear a (sphereAt γ y) →
      ∃ ε : ℝ, 0 < ε ∧ ∃ u : ℝ → (X dim) → ℝ,
        ContinuousOn (fun p : ℝ × ↥(standardSphere dim) =>
          u p.1 (endpoint E r (y,frameVector e y p.2)))
          (Icc (0 : ℝ) ε ×ˢ (univ : Set ↥(standardSphere dim))) ∧
        (∀ w : ↥(standardSphere dim), u 0 (endpoint E r (y,frameVector e y w)) = a (frameVector e y w)) ∧
        ∀ t ∈ Ioc (0 : ℝ) ε, ∃ U : Set (X dim), IsOpen U ∧ closedBallImage γ E r y ⊆ U ∧ Harmonic U g (u t)) :
    ∀ w : ↥(standardSphere dim), φ (y,frameVector e y w) = 0 := by
  obtain ⟨S,hS,hSub,hφS⟩ := hφ
  let F (w : (X dim)) := (y,w)
  let V := F ⁻¹' S
  have hF : ContDiff ℝ ∞ F := contDiff_const.prodMk contDiff_id
  have hV : IsOpen V := hS.preimage hF.continuous
  have hSV : sphereAt γ y ⊆ V := fun _ hw => hSub ⟨hy,hw⟩
  have hφV : ContDiffOn ℝ ∞ (fun w : (X dim) => φ (y,w)) V := hφS.comp hF.contDiffOn (fun _ h => h)
  let v (w : ↥(standardSphere dim)) := φ (y,frameVector e y w)
  have hv : Continuous v := hφV.continuousOn.comp_continuous
    ((continuous_frameVector e y).comp continuous_subtype_val)
    (fun w => hSV (frameVector_mem_sphere γ e y he w))
  obtain ⟨ε₁,hε₁,u₁,hC₁,hD₁,hU₁⟩ := hApprox (fun w => (φ (y,w)).re)
    ⟨V,hV,hSV,Complex.reCLM.contDiff.comp_contDiffOn hφV⟩
  obtain ⟨ε₂,hε₂,u₂,hC₂,hD₂,hU₂⟩ := hApprox (fun w => (φ (y,w)).im)
    ⟨V,hV,hSV,Complex.imCLM.contDiff.comp_contDiffOn hφV⟩
  let ε := min ε₁ ε₂
  let b (p : ℝ × ↥(standardSphere dim)) := u₁ p.1 (endpoint E r (y,frameVector e y p.2))
  let c (p : ℝ × ↥(standardSphere dim)) := u₂ p.1 (endpoint E r (y,frameVector e y p.2))
  have he₁ : ε ≤ ε₁ := min_le_left _ _
  have he₂ : ε ≤ ε₂ := min_le_right _ _
  have hEq := complex_eq_zero_of_enlarged_trace_duality hv (lt_min hε₁ hε₂) b c
    (hC₁.mono (prod_mono (Icc_subset_Icc_right he₁) Subset.rfl))
    (hC₂.mono (prod_mono (Icc_subset_Icc_right he₂) Subset.rfl)) hD₁ hD₂
    (fun t ht => by
      obtain ⟨U,hU,hB,hH⟩ := hU₁ t ⟨ht.1,ht.2.trans he₁⟩
      exact hAnn hU hB hH)
    (fun t ht => by
      obtain ⟨U,hU,hB,hH⟩ := hU₂ t ⟨ht.1,ht.2.trans he₂⟩
      exact hAnn hU hB hH)
  exact fun w => congrFun hEq w

end CalderonN
