import Proof.ActualHighRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- The actual smooth physical harmonic pullback is the strong Poisson solution
    with the same boundary datum. This holds for every compact representative
    of the actual coefficient, independently of its exterior extension. -/
theorem uniform_physical_strong_poisson_realization {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ F : SmoothCoefficientMatrix 2,
      (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x]
        (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) →
      (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible →
      ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∀ f : SphereSobolev (3/2:ℝ),
      (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
        u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
      ∃ U : SmoothData,HasCompactSupport U.1 ∧
        (∀ z ∈ Metric.closedBall (0:X) 1,U.1 =ᶠ[𝓝 z]
          (u ∘ normalChart d.expMap d.frame y (d.radius y))) ∧
        smoothBallSobolev 2 U = strongPoissonL F f := by
  obtain ⟨ηR,hηR,hRepresentative⟩ := uniform_normal_weak_harmonic_representative
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηR ηE,lt_min hηR hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy F hRep hInv u hu f hBoundary
  have hHere := hRepresentative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy u hu
  obtain ⟨U,hCompact,hNear,hWeak⟩ := hHere
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) 2) (4*K^2) H :=
    hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  obtain ⟨hCoefficient,hCoercive,hInverse⟩ := hEll.unitBall_dirichlet_data hKP
  have hPoint (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F x = principalCoefficient H x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hUTrace : fixedUnitBallValueTrace.valueTraceL (smoothSobolev U) =ᵐ[sphereProbability]
      fun w : UnitSphere => u (normalChart d.expMap d.frame y (d.radius y) w.val) := by
    rw [fixedUnitBallValueTrace.valueTrace_smooth]
    filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (μ:=sphereProbability) (𝕜:=ℝ) (smoothSphereValue U)] with w hw
    have hClosed : w.val ∈ Metric.closedBall (0:X) 1 := by
      have hn : ‖w.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using w.property
      simpa [Metric.mem_closedBall,dist_zero_right,hn]
    exact hw.trans (hNear w.val hClosed).eq_of_nhds
  have hTrace : fixedUnitBallValueTrace.valueTraceL (smoothSobolev U) =
      fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)) := by
    rw [fixedBoundaryValueL_harmonicLift]
    exact Lp.ext (hUTrace.trans hBoundary.symm)
  exact ⟨U,hCompact,hNear,strongPoissonL_eq_smooth_harmonic hCoefficient hCoercive F hPoint hInv f U hWeak hTrace⟩

end ShrinkingSpheres
