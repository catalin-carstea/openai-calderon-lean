import Proof.BoundaryPoissonTrace
import Proof.UniformHighRadialEndpoint
import Proof.ActualRadialTraceBridge

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

/-- The uniformly controlled completed high endpoint is the actual physical
    radial Dirichlet response for every boundary datum realized by a smooth
    physical harmonic solution. No trace-kernel or PDE premise is added. -/
theorem uniform_physical_high_radial_endpoint {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CH : ℝ,0 < η ∧ 0 ≤ CH ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F : SmoothCoefficientMatrix 2,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
          coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => principalCoefficient
            (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ∀ u : X → ℝ,
        HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
        ∀ f : SphereSobolev (3/2:ℝ),
        (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
          u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
        (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL F f)
          =ᵐ[sphereProbability] fun w : UnitSphere =>
            radialTrace d.expMap d.radius y (frameVector d.frame y w.val) u) ∧
        ‖fixedHalfOutwardTraceL (strongPoissonL F f)-fixedHalfOutwardTraceL (fixedHarmonicLiftL f)‖ ≤
          CH*d.radius y*‖f‖ := by
  obtain ⟨ηH,CH,hηH,hCH,hH⟩ := uniform_actual_high_radial_endpoint
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,hηR,hR⟩ := uniform_normal_weak_harmonic_representative
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηH (min ηR ηE),CH,lt_min hηH (lt_min hηR hηE),hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hSH := hSmall.trans (min_le_left _ _)
  have hSR := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨F,hRep,hInv,hNorm⟩ := hH floor hf ε hε hSH d hd y hy
  refine ⟨F,hRep,hInv,?_⟩
  intro u hu f hBoundary
  obtain ⟨U,hComp,hNear,hWeak⟩ := hR floor hf ε hε hSR d hd y hy u hu
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) 2) (4*K^2) H :=
    hE floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  obtain ⟨hcoeff,hCoerce,hInverse⟩ := hEll.unitBall_dirichlet_data hKP
  have hPoint (x : X) (hx : x ∈ (ballOpens : Set X)) :
      coefficientMatrixField 2 F x = principalCoefficient H x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hUTrace : fixedUnitBallValueTrace.valueTraceL (smoothSobolev U)
      =ᵐ[sphereProbability] fun w : UnitSphere => u (normalChart d.expMap d.frame y (d.radius y) w.val) := by
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
  have hIdent := strongPoissonL_eq_smooth_harmonic (a:=principalCoefficient H)
    hcoeff hCoerce F hPoint hInv f U hWeak hTrace
  have hActual := hd.outwardRadialTrace_representative_ae hY hy u hu U hNear
  rw [hIdent] at hActual
  refine ⟨hActual,?_⟩
  have hb := ((fixedHalfOutwardTraceL.comp (strongPoissonL F)-
    fixedHalfOutwardTraceL.comp fixedHarmonicLiftL).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hNorm (norm_nonneg f))
  simpa only [_root_.sub_apply,ContinuousLinearMap.comp_apply] using hb

end ShrinkingSpheres
