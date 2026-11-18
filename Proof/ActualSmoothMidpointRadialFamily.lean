import Proof.ActualLocalRadialFamily
import Proof.ActualMidpointRadialUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- A single smooth family of the actual H1-to-L2 radial error, independent
    of all local coefficient extensions. No derivative norm bound is asserted. -/
theorem uniform_actual_smooth_midpoint_radial_family {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∃ R : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ContDiffOn ℝ ∞ R Y ∧ ∀ y ∈ Y,RealizesActualMidpointRadialError d y (R y) := by
  classical
  obtain ⟨η,hη,hLocal⟩ := uniform_actual_normal_local_radial_family hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd
  have hLoc (y : X) (hy : y ∈ Y) :
      ∃ V : Set X,IsOpen V ∧ y ∈ V ∧ V ⊆ Y ∧
        ∃ R : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
          ContDiffOn ℝ ∞ R V ∧ ∀ p ∈ V,
            RealizesActualMidpointRadialError d p (R p) ∧
              ∃ F : SmoothCoefficientMatrix 2,∀ z ∈ (ballOpens : Set X),coefficientMatrixField 2 F z =
                principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap p (d.radius p)) z := by
    obtain ⟨A,hA,S,hS,hz,V,hV,hyV,hVY,hRep,R,hSmooth,hRestriction⟩ :=
      hLocal floor hf ε hε hSmall d hd y hy
    refine ⟨V,hV,hyV,hVY,R,hSmooth,?_⟩
    intro p hp
    let F := commonSupportMatrixFamily 2 A hA S hS hz p
    have hF (z : X) (hzBall : z ∈ (ballOpens : Set X)) : coefficientMatrixField 2 F z =
        principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap p (d.radius p)) z := by
      simp only [F,coefficientMatrixField_commonSupportMatrixFamily]
      exact (hRep p hp z (unitBall_subset_closedBall_two hzBall)).eq_of_nhds
    exact ⟨realizesActualMidpointRadialError_of_restriction d p (R p) F hF (hRestriction p hp),F,hF⟩
  have hPoint (y : X) (hy : y ∈ Y) : ∃ R,RealizesActualMidpointRadialError d y R := by
    obtain ⟨V,hV,hyV,hVY,R,hSmooth,hRealizes⟩ := hLoc y hy
    exact ⟨R y,(hRealizes y hyV).1⟩
  let R : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun y =>
    if hy : y ∈ Y then Classical.choose (hPoint y hy) else 0
  have hRealizes (y : X) (hy : y ∈ Y) : RealizesActualMidpointRadialError d y (R y) := by
    dsimp only [R]
    rw [dif_pos hy]
    exact Classical.choose_spec (hPoint y hy)
  refine ⟨R,?_,hRealizes⟩
  intro y hy
  obtain ⟨V,hV,hyV,hVY,T,hSmooth,hT⟩ := hLoc y hy
  have hEq : R =ᶠ[𝓝 y] T := by
    filter_upwards [hV.mem_nhds hyV] with p hp
    obtain ⟨hTp,F,hF⟩ := hT p hp
    exact (hRealizes p (hVY hp)).unique d p (R p) (T p) hTp F hF
  exact ((hSmooth.contDiffAt (hV.mem_nhds hyV)).congr_of_eventuallyEq hEq).contDiffWithinAt

end ShrinkingSpheres
