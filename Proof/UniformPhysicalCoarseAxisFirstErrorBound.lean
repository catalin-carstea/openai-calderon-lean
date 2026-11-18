import Proof.UniformPhysicalPrincipalData
import Proof.UniformActualFirstAdjointError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The shared axis bound extracted from the existing physical frame-error
producer. Actual center-adjoint uniqueness keeps ANY selected P witnesses. -/
theorem uniform_physical_coarse_axis_first_error_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ a : I,∀ y ∈ Y,
        ‖actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) y‖ ≤ CE*d.radius y := by
  classical
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hError⟩ :=
    uniform_actual_smooth_first_adjoint_error hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηE ηC,CE,lt_min hηE hηC,(min_le_left _ _).trans hηE1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P a y hy
  obtain ⟨G,hGS,hG,hES,hEN⟩ := hError floor hf ε hε (hSmall.trans (min_le_left _ _))
    d hd P.radial P.adjoint P.adjoint_smooth P.radial_actual P.adjoint_pair (axis a)
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH :=
    fun j => Classical.choice (hCoeff floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy (axis a) j)
  let W : I → SmoothCoefficientJets 2 := fun j => (C j).pointCoefficient
  have hW (j : I) (w : UnitSphere) : coefficientValue 2 (W j) w.val=actualCenterErrorWeight d y (axis a) j w.val := by
    have hw2 : w.val ∈ Metric.closedBall (0:X) 2 :=
      Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
    exact ((C j).point_coefficient_actual w.val hw2).eq_of_nhds
  have hEq := RealizesActualCenterGradientAdjoint.unique d y (axis a) (P.adjoint y) (P.center a y) (G y)
    (P.center_actual a y hy) (hG y hy) W hW
  have hN := hEN y hy
  rw [norm_axis,mul_one] at hN
  simpa only [actualFirstAdjointErrorFamily,hEq] using hN

end ShrinkingSpheres
