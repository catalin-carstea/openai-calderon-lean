import Proof.WeakFluxIntegration

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.MetricOperator OAI.AnisotropicCalderon.ConnectionError

/-- Classical divergence-free smooth representatives satisfy the actual weak
    equation against all zero-boundary Sobolev tests. -/
theorem Elliptic.smoothSobolev_weak_equation {K : ℝ} {g : MetricField}
    (hg : Elliptic (Metric.closedBall (0:X) 2) K g) (hK : 0 < K)
    (U : SmoothData)
    (hDiv : ∀ z ∈ (ballOpens : Set X),coordinateFluxDivergence (metricDivergenceFlux g U.1) z = 0)
    (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (smoothSobolev U) (v : BallH1) = 0 := by
  have hA : ContDiffOn ℝ ∞ (principalCoefficient g) (Metric.ball (0:X) 2) :=
    (hg.contDiffOn_principalCoefficient hK).mono Metric.ball_subset_closedBall
  have hFlux : ContDiffOn ℝ ∞ (metricDivergenceFlux g U.1) (Metric.ball (0:X) 2) :=
    (matrixOperatorMap.contDiff.comp_contDiffOn hA).clm_apply
      (contDiff_actual_scalarGradient U.1 U.2).contDiffOn
  have h12 : Metric.closedBall (0:X) 1 ⊆ Metric.ball (0:X) 2 := by
    intro z hz
    change dist z 0 < 2
    change dist z 0 ≤ 1 at hz
    exact hz.trans_lt (by norm_num)
  obtain ⟨F,hF,_,hNear⟩ := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.closedBall (0:X) 1) (Metric.ball (0:X) 2) (isCompact_closedBall _ _)
    Metric.isOpen_ball h12 (metricDivergenceFlux g U.1) hFlux
  have hPoint (z : X) (hz : z ∈ (ballOpens : Set X)) :
      F z = matrixOperatorMap (principalCoefficient g z) (gradient U.1 z) :=
    (hNear z (Metric.ball_subset_closedBall hz)).eq_of_nhds
  have hZero (z : X) (hz : z ∈ (ballOpens : Set X)) : coordinateFluxDivergence F z = 0 :=
    (coordinateFluxDivergence_congr_germ (hNear z (Metric.ball_subset_closedBall hz))).trans (hDiv z hz)
  exact smooth_flux_weak_equation (principalCoefficient g) U F hF hPoint hZero v

/-- A genuine smooth Sobolev representative of every admitted physical harmonic
    solution satisfies the actual weak harmonic equation against zero-boundary tests. -/
theorem uniform_normal_weak_harmonic_representative {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ u : X → ℝ,
      HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∃ U : SmoothData,HasCompactSupport U.1 ∧
        (∀ z ∈ Metric.closedBall (0:X) 1,U.1 =ᶠ[𝓝 z] (u ∘ normalChart d.expMap d.frame y (d.radius y))) ∧
        ∀ v : BallH1Zero,TauCeti.PDE.energyFormH1
          (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)))
          0 0 (smoothSobolev U) (v : BallH1) = 0 := by
  obtain ⟨ηR,hηR,hR⟩ := uniform_normal_harmonic_representative (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηR ηE,lt_min hηR hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy u hu
  obtain ⟨U,hComp,hNear,hDiv⟩ := hR floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy u hu
  have hEll := hE floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy d.g₁ (by simp)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  exact ⟨U,hComp,hNear,fun v => hEll.smoothSobolev_weak_equation (by positivity) U hDiv v⟩

end ShrinkingSpheres
