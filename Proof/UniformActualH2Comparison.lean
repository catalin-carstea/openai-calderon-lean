import Proof.H2BoundaryComparison
import Proof.SmoothFlatHarmonic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.ConnectionError
open OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility

/-- The actual physical harmonic pullback has a common radius-linear H2
    comparison with every smooth Euclidean harmonic extension of its boundary
    data. All constants are chosen before the arbitrary admitted profile. -/
theorem uniform_euclidean_harmonic_H2_comparison {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CH : ℝ,0 < η ∧ 0 ≤ CH ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ u : X → ℝ,
      HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∀ V : SmoothData,
      (∀ z : X,‖z‖ = 1 → u (normalChart d.expMap d.frame y (d.radius y) z) = V.1 z) →
      (∀ z ∈ (ballOpens : Set X),coordinateFluxDivergence (gradient V.1) z = 0) →
      ∃ U : SmoothData,HasCompactSupport U.1 ∧
        (∀ z ∈ Metric.closedBall (0:X) 1,
          U.1 =ᶠ[𝓝 z] (u ∘ normalChart d.expMap d.frame y (d.radius y))) ∧
        ‖smoothBallSobolev 2 U-smoothBallSobolev 2 V‖ ≤
          CH*d.radius y*‖smoothBallSobolev 2 V‖ := by
  obtain ⟨ηS,C,hηS,hC,hS⟩ := uniform_actual_strong_dirichlet_lifts
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,Q,F0,hηF,hQ,hF0,hF⟩ := uniform_actual_local_flat_comparison
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,hηR,hR⟩ := uniform_normal_weak_harmonic_representative
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let B := fullC1OperatorBudget fixedSobolevCalculus
  have hB : 0 ≤ B := fullC1OperatorBudget_nonneg _
  refine ⟨min ηS (min ηF (min ηR ηE)),C*B*Q,
    lt_min hηS (lt_min hηF (lt_min hηR hηE)),mul_nonneg (mul_nonneg hC hB) hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy u hu V hBoundary hFlat
  have hSS := hSmall.trans (min_le_left _ _)
  have hSF := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSR := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSE := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  obtain ⟨U,hComp,hNear,hWeak⟩ := hR floor hf ε hε hSR d hd y hy u hu
  have hLifts : StrongDirichletLiftData (principalCoefficient H) C := hS floor hf ε hε hSS d hd y hy
  obtain ⟨F,c,hcPos,hRep,hValue,hDerivative⟩ := hF floor hf ε hε hSF d hd y hy
  have hEll : Elliptic (Metric.closedBall (0:X) 2) (4*K^2) H :=
    hE floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  obtain ⟨hcoeff,hCoerce,hInverse⟩ := hEll.unitBall_dirichlet_data hKP
  have hPoint (x : X) (hx : x ∈ (ballOpens : Set X)) :
      coefficientMatrixField 2 F x = principalCoefficient H x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hBoundaryU (z : X) (hz : ‖z‖ = 1) : U.1 z = V.1 z := by
    have hClosed : z ∈ Metric.closedBall (0:X) 1 := by simpa [Metric.mem_closedBall,dist_zero_right,hz]
    exact (hNear z hClosed).eq_of_nhds.trans (hBoundary z hz)
  have hF0Ball (x : X) (hx : x ∈ (ballOpens : Set X)) : coefficientMatrixField 2 F0 x = 1 :=
    hF0 x (unitBall_subset_closedBall_two hx)
  have hFlatOp : fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0) (smoothBallSobolev 2 V) = 0 := by
    rw [map_smul,ContinuousLinearMap.smul_apply,fullCoefficientOperator_flat_eq fixedSobolevCalculus F0 hF0Ball]
    simp only [ContinuousLinearMap.neg_apply,nativeEuclideanLaplacian_smooth_eq_zero fixedSobolevCalculus V hFlat,
      neg_zero,smul_zero]
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hBound := norm_smooth_harmonic_correction_of_local_C1 (a:=principalCoefficient H) hC hcoeff hCoerce
    hLifts F F0 c (Q*d.radius y) (mul_nonneg hQ hr.le) hPoint hValue hDerivative U V hBoundaryU hWeak hFlatOp
  exact ⟨U,hComp,hNear,hBound.trans_eq (by dsimp only [B];ring)⟩

end ShrinkingSpheres
