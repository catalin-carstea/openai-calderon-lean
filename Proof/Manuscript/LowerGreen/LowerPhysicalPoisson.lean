module

public import Proof.Manuscript.LowerGreen.KnownNormalGreenEvaluation
public import Proof.Manuscript.LowerGreen.SphereDensityUniqueness
public import Proof.Manuscript.LowerGreen.BallCutoffChains
public import Proof.CalderonN.MovingGreenFluxDensity

import Proof.CalderonN.ActualEnlargedNormalTrace
import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.FrameOperators
import Proof.CalderonN.MovingBallFamilies
import Proof.CalderonN.MetricBallDirichlet
import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric MeasureTheory CalderonN CalderonN.BallDirichlet
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

set_option maxHeartbeats 2900000 in
/-- The first-side Green flux on a known lower sphere is the center
Poisson density of the same normalized metric. -/
theorem movingGreenFlux_eq_normalizedPoisson
    {Y Ω : Set (X n)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ g₁ g₂ : MetricField n} (hγ : SmoothMetric univ γ) (hg : SmoothMetric univ g₁)
    {ρ : ℝ} {E : X n × X n → X n} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {O : Set (X n × X n)} (hO : IsOpen O) {G K : X n × X n → ℝ}
    (hG : ProductSolutionOn g₁ g₂ O G) (hK : GreenGerm Ω g₁ K)
    {e : Frame n} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (hec : ∀ i, ContinuousOn (fun y => e y i) Y) {r : X n → ℝ}
    (hrc : ContinuousOn r Y) (hr : ∀ y ∈ Y, 0 < r y ∧ r y < ρ)
    {y : X n} (hy : y ∈ Y)
    (hSphere : ∀ w : ↥(standardSphere n), (E (y,r y • frameVector e y w),y) ∈ O)
    (hKnown : ∀ x, (x,y) ∈ normalPairDomain Y γ ρ E → x ≠ y → G (x,y) = K (x,y))
    {ψ : X n × X n → ℝ}
    (hψ : Continuous (fun w : ↥(standardSphere n) => ψ (y,frameVector e y w)))
    (hFlux : ∀ u, HarmonicOnBall g₁ (closedBallImage γ E r y) u →
      (∫ w : ↥(standardSphere n), ψ (y,frameVector e y w) * u (endpoint E r (y,frameVector e y w))
        ∂(sphereProbability n)) = normalSphereGreenFlux g₁ E e r G y u)
    {D : Set (X n)} (hD : IsOpen D) (hCD : closedBall (0 : X n) 1 ⊆ D)
    (hM : SmoothMetric D (fun z => movingBallMetric g₁ E e r (y,z)))
    (F : SupportedBallFamily P n) {p : P}
    (hA : ∀ z ∈ D, ∀ i j, F.a (p,z) i j =
      divergenceCoeff (fun x => movingBallMetric g₁ E e r (y,x)) z i j)
    {π : ↥(standardSphere n) → ℝ} (hπ : Continuous π)
    (hRep : ∀ u : SmoothData n, EqOn (negativeBallDivergence (fun z => F.a (p,z)) u.1) 0
      (ball (0 : X n) 1) → ∫ w, π w * u.1 w ∂(sphereProbability n) = u.1 0) :
    ∀ w : ↥(standardSphere n), ψ (y,frameVector e y w) = π w := by
  suffices h : (fun w : ↥(standardSphere n) => ψ (y,frameVector e y w)) = π from congrFun h
  let chart := normalBallChartMap E e y (r y)
  let m := fun z => movingBallMetric g₁ E e r (y,z)
  have hgΩ := smoothMetric_restrict hg (subset_univ Ω)
  have h0 : chart 0 = y := by
    have hDisk : (0 : X n) ∈ disk γ y ρ := by simp [disk,metricPair,sq_nonneg]
    have hCenter := ((hN.2 y hy).2.2 0 hDisk).2.2.1
    simpa [chart,normalBallChartMap,frameVector] using hCenter
  have hEval {U : Set (X n)} (hU : IsOpen U) (hCover : closedBallImage γ E r y ⊆ U)
      {u : X n → ℝ} (hu : Harmonic U g₁ u) :
      (∫ w : ↥(standardSphere n), ψ (y,frameVector e y w) * u (endpoint E r (y,frameVector e y w))
        ∂(sphereProbability n)) =
        ∫ w : ↥(standardSphere n), π w * u (endpoint E r (y,frameVector e y w))
          ∂(sphereProbability n) := by
    have huBall : HarmonicOnBall g₁ (closedBallImage γ E r y) u :=
      ⟨⟨U,hU,hCover,hu.1⟩,fun z hz => hu.2 z (hCover (interior_subset hz))⟩
    rw [hFlux u huBall,knownNormalGreenFlux_eq_value hY hΩ hγ hgΩ hE hN hO hG hK he hec hrc hr hy
      hSphere hKnown hU hCover hu]
    obtain ⟨D',hD',hCD',_,huD',hLap⟩ :=
      harmonicOnBall_normalBallChartMap hΩ hgΩ hE hN hy (he y hy) (hr y hy).1 (hr y hy).2 huBall
    obtain ⟨v,hv,_,V,hV,hCV,hVD',hEq⟩ := exists_contDiff_extension_near_compact hD'
      (isCompact_closedBall (0 : X n) 1) hCD' huD'
    let b : SmoothData n := ⟨v,hv⟩
    have hLapM (z : X n) (hz : z ∈ ball (0 : X n) 1) : laplace m b.1 z = 0 := by
      have hzD := hCD (ball_subset_closedBall hz)
      have hzV := hCV (ball_subset_closedBall hz)
      have hC := laplace_pullback_normalizedBall hE (hr y hy).1 hD hzD hM (u ∘ chart)
      have hP := hLap z hz
      change laplace (pullbackMetric g₁ chart) (u ∘ chart) z = 0 at hP
      change laplace (pullbackMetric g₁ chart) (u ∘ chart) z =
        (r y ^ 2)⁻¹ * laplace m (u ∘ chart) z at hC
      rw [hP] at hC
      have hM₀ := (mul_eq_zero.mp hC.symm).resolve_left (inv_ne_zero (pow_ne_zero _ (hr y hy).1.ne'))
      exact (laplace_congrOn hV (fun _ _ => rfl) hEq hzV).trans hM₀
    have hDivergence : EqOn (negativeBallDivergence (fun z => F.a (p,z)) b.1) 0
        (ball (0 : X n) 1) := by
      intro z hz
      have h := negativeBallDivergence_eq_neg_laplace hD hM hA hv.contDiffOn (hCD (ball_subset_closedBall hz))
      rw [hLapM z hz,mul_zero,neg_zero] at h
      exact h
    have hCenter : b.1 0 = u y := by
      change v 0 = _
      exact (hEq (hCV (mem_closedBall_self zero_le_one))).trans (congrArg u h0)
    have hTrace (w : ↥(standardSphere n)) : b.1 w = u (endpoint E r (y,frameVector e y w)) :=
      hEq (hCV (sphere_subset_closedBall w.property))
    have h := hRep b hDivergence
    rw [hCenter] at h
    simpa only [hTrace] using h.symm
  apply sphereDensity_eq_of_smooth_pairings hψ hπ
  intro a ha
  let a' : X n → ℝ := a ∘ frameCoordinatesL γ y (e y)
  have ha' : ContDiff ℝ ∞ a' := ha.comp (frameCoordinatesL γ y (e y)).contDiff
  obtain ⟨ε,hε,u,hTrace,hZero,hU⟩ := exists_enlarged_normalTrace_family hg hE hN hy
    (he y hy) (hr y hy).1 (hr y hy).2 (⟨univ,isOpen_univ,subset_univ _,ha'.contDiffOn⟩ :
      smoothNear a' (sphereAt γ y))
  have hP := spherePair_eq_at_zero_of_positive hψ hπ hε hTrace (fun t ht => by
    obtain ⟨U,hU',hCover,hu⟩ := hU t ht
    exact hEval hU' hCover hu)
  have hTraceZero (w : ↥(standardSphere n)) : u 0 (endpoint E r (y,frameVector e y w)) = a w := by
    have hv := frameCoordinatesL_frameVectorL γ y (e y) (he y hy) w
    rw [frameVectorL_apply (e y) w y] at hv
    exact (hZero w).trans (congrArg a hv)
  simpa only [hTraceZero] using hP

end CalderonPaper.LowerGreen

end
