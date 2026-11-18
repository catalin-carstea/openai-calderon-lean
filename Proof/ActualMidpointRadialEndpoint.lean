import Proof.RadialEndpointCompatibility
import Proof.UniformHighRadialEndpoint
import Proof.Archive.SphereSobolevMidpointExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- The Poisson construction is independent of the exterior compact extension. -/
theorem strongPoissonL_congr_on_ball (F G : SmoothCoefficientMatrix 2)
    (hFG : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = coefficientMatrixField 2 G x) :
    strongPoissonL F = strongPoissonL G := by
  have hStrong := strongDirichletOperator_congr_on_ball fixedSobolevCalculus 0 F G hFG
  have hFull := fullCoefficientOperator_congr_on_ball fixedSobolevCalculus 0 F G hFG
  apply ContinuousLinearMap.ext
  intro f
  rw [strongPoissonL_apply,strongPoissonL_apply,hStrong,hFull]

/-- Midpoint interpolation gives the actual common H1-to-L2 radial error.
    Its restriction to H3/2 data is exactly the genuine strong radial error. -/
theorem uniform_actual_midpoint_radial_endpoint {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CM : ℝ,0 < η ∧ 0 ≤ CM ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F : SmoothCoefficientMatrix 2,∃ R : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
          coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => principalCoefficient
            (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖R‖ ≤ CM*d.radius y ∧
        R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F) := by
  obtain ⟨ηL,CL,hηL,hCL,hLow⟩ := uniform_actual_low_radial_endpoint
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηH,CH,hηH,hCH,hHigh⟩ := uniform_actual_high_radial_endpoint
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηL ηH,(CL+CH)/2,lt_min hηL hηH,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨F,e,hRep,hInv,hNormal,hLowNorm⟩ :=
    hLow floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨FH,hRepH,hInvH,hHighNorm⟩ :=
    hHigh floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
  let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
  have hPoint (x : X) (hx : x ∈ (ballOpens : Set X)) : coefficientMatrixField 2 F x = a x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
  have hFG (x : X) (hx : x ∈ (ballOpens : Set X)) :
      coefficientMatrixField 2 F x = coefficientMatrixField 2 FH x := by
    ext i j
    exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.trans
      (hRepH x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds.symm
  have hPoisson := strongPoissonL_congr_on_ball F FH hFG
  have hHighF : ‖actualHighRadialErrorL F‖ ≤ CH*d.radius y := by
    rw [actualHighRadialErrorL,hPoisson]
    exact hHighNorm
  let T0 := actualLowRadialErrorL a e.coefficient_bound F
  let T1 := actualHighRadialErrorL F
  have hCompat := actual_radial_endpoints_compatible e.coefficient_bound e.coercive F hPoint hInv hNormal
  have hCompatM : (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp T1 =
      T0.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    have hIndex : (-1/2:ℝ) = -(1/2:ℝ) := by ring
    have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
      (by norm_num) (by norm_num) hIndex
    exact (congrArg (fun J : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => J.comp T1) hI).trans hCompat
  refine ⟨F,sphereSobolevMidpointL T0 T1 hCompatM,hRep,hInv,?_,?_⟩
  · exact (norm_sphereSobolevMidpointL_le T0 T1 hCompatM).trans (by
      have hSum := add_le_add hLowNorm hHighF
      nlinarith only [hSum])
  · exact sphereSobolevMidpointL_inclusion T0 T1 hCompatM

end ShrinkingSpheres
