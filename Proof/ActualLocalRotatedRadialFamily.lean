import Proof.RotatedRadialFamily
import Proof.LocalCommonSupportCoefficientFamily
import Proof.ActualMidpointRadialUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Actual geometric radial errors admit a genuine smooth whole-angle
    family on a common local center set. One coefficient representative and
    one spatial support serve every angle; the zero-angle map is the actual
    cutoff-independent radial response. -/
theorem uniform_actual_normal_local_rotated_radial_family {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A : X × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ L : ℝ,2 ≤ L ∧
      ∃ hz : ∀ p z,z ∉ Metric.closedBall (0:X) L → A (p,z) = 0,
      ∃ V : Set X,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
        (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (p,z)]
          (fun q : X × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap q.1
            (d.radius q.1)) q.2)) ∧
        ∀ i j : I,∃ R : (ℝ × X) → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
          ContDiffOn ℝ ∞ R (Set.univ ×ˢ V) ∧
          (∀ t ∈ Set.univ ×ˢ V,(R t).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
              (actualHighRadialErrorL (rotatedCommonSupportMatrixFamily i j A hA L hz t))) ∧
          (∀ p ∈ V,RealizesActualMidpointRadialError d p (R (0,p))) ∧
          ∀ θ : ℝ,∀ p ∈ V,(R (θ,p)).comp (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ)) =
            (sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ)).comp (R (0,p)) := by
  obtain ⟨ηF,hηF,hFamily⟩ := uniform_actual_normal_local_coefficient_family hY hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηF ηE,lt_min hηF hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hHere := hFamily floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy d.g₁ (by simp)
  obtain ⟨A,hA,S,hS,hz,V,hV,hyV,hVY,hRep⟩ := hHere
  have hId : ContinuousOn (fun z : X => z) S := continuous_id.continuousOn
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hId
  let L := max B 2
  have hL : 2 ≤ L := le_max_right _ _
  have hzBall (p z : X) (hzL : z ∉ Metric.closedBall (0:X) L) : A (p,z) = 0 := by
    apply hz p z
    intro hzS
    apply hzL
    change dist z 0 ≤ L
    rw [dist_zero_right]
    exact (hB z hzS).trans (le_max_left _ _)
  let KP := 4*K^2
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith [sq_nonneg (K-1)]
  let lam := (metricDensityBudget KP)⁻¹*KP⁻¹
  let Lam := metricDensityBudget KP*KP
  have hUE (p : X) (hp : p ∈ V) :
      TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (fun z => A (p,z)) lam Lam := by
    have hEll := hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd p (hVY hp) d.g₁ (by simp)
    have hU := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
    refine ⟨hU.1,hU.2.1,?_⟩
    intro z hzB
    simp only [(hRep p hp z (unitBall_subset_closedBall_two hzB)).eq_of_nhds]
    exact hU.2.2 hzB
  refine ⟨A,hA,L,hL,hzBall,V,hV,hyV,hVY,hRep,?_⟩
  intro i j
  obtain ⟨R,hSmooth,hRestrict,hCov⟩ := exists_smooth_rotated_midpoint_radial_family
    i j A hA L hzBall V hV lam Lam hUE
  refine ⟨R,hSmooth,hRestrict,?_,hCov⟩
  intro p hp
  let F := rotatedCommonSupportMatrixFamily i j A hA L hzBall (0,p)
  have hF (z : X) (hzB : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap p (d.radius p)) z := by
    simp only [F,coefficientMatrixField_rotatedCommonSupportMatrixFamily,coordinateRotationPrincipalFamily_zero_angle]
    exact (hRep p hp z (unitBall_subset_closedBall_two hzB)).eq_of_nhds
  exact realizesActualMidpointRadialError_of_restriction d p (R (0,p)) F hF
    (hRestrict (0,p) ⟨mem_univ _,hp⟩)

end ShrinkingSpheres
