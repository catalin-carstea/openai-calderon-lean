import Proof.RelativeRadiusCoefficientModel
import Proof.JointMetricCoefficientRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  fullCoefficientOperatorL strongCoefficientOperatorL

/-- Every admitted profile supplies the actual relative-radius family,
    its SAME linear first model and quadratic residual, with all native
    parameter derivative budgets. The relative-radius derivative preserves r². -/
theorem uniform_relative_radius_coefficient_generators {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C1 CQ : ℝ,0 < η ∧ 0 ≤ C1 ∧ 0 ≤ CQ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A A1 D : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,∃ hD : ContDiff ℝ ∞ D,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (t,z)]
        relativeDilationFamily (normalizedFirstNormalCoefficient d y)) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (t,z)]
        relativeDilationFamily (scalarFirstCoefficient (firstDensityLogCovector d y))) ∧
      (∀ p,D p = A p-d.radius y • A1 p) ∧
      ∃ b1 : X → Mat,∃ hb1 : ContDiff ℝ ∞ b1,∃ hzb1 : ∀ z,z ∉ S → b1 z = 0,
      (∀ z,HasDerivAt (fun t => A1 (t,z)) (b1 z) 0) ∧
      (∀ z ∈ (ballOpens:Set X),‖b1 z‖ ≤ C1) ∧ (∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b1 z‖ ≤ C1) ∧
      ∃ bD : X → Mat,∃ hbD : ContDiff ℝ ∞ bD,∃ hzbD : ∀ z,z ∉ S → bD z = 0,
      (∀ z,HasDerivAt (fun t => D (t,z)) (bD z) 0) ∧
      (∀ z ∈ (ballOpens:Set X),‖bD z‖ ≤ CQ*(d.radius y)^2) ∧
      (∀ z ∈ (ballOpens:Set X),‖fderiv ℝ bD z‖ ≤ CQ*(d.radius y)^2) ∧
      ∀ t ∈ V,∀ w : UnitSphere,A1 (t,w.val) = ((1+t) • firstDensityLogCovector d y) w.val • (1:Mat) := by
  obtain ⟨ηC,Q,B,hηC,hQ,hB,hC2⟩ := uniform_normalized_coefficient_remainder_C2 hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,hηS,hSmooth⟩ := uniform_framed_normal_coefficient_joint_regular hY hΩ (by omega)
    K ρ c₀ M Cj hK hρ 3 (by norm_num)
  let C1 := K^2*|M ⟨1,by omega⟩|
  let CQ := Q+B
  have hC1 : 0 ≤ C1 := by dsimp only [C1];positivity
  have hCQ : 0 ≤ CQ := add_nonneg hQ hB
  refine ⟨min ηC (min ηS 1),C1,CQ,lt_min hηC (lt_min hηS zero_lt_one),hC1,hCQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  let r := d.radius y
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ell := firstDensityLogCovector d y
  let f := normalizedFirstNormalCoefficient d y
  let f1 := scalarFirstCoefficient ell
  let R := normalizedFirstCoefficientRemainder d y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hEll : ‖ell‖ ≤ C1 := hd.1.norm_firstDensityLogCovector_le hΩ hK (by omega) (hd.2.1.center_mem hy)
  have hfAt (z : X) (hzB : z ∈ Metric.closedBall (0:X) 3) : ContDiffAt ℝ ∞ f z := by
    have hPrincipal : ContDiffAt ℝ ∞
        (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r)) z := by
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      have hJoint := hSmooth floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
        d hd y hy d.g₁ (by simp) z hzB i j
      exact hJoint.comp z (contDiffAt_const.prodMk contDiffAt_id)
    exact hPrincipal.const_smul c⁻¹
  have hfOn : ContDiffOn ℝ ∞ f (Metric.ball (0:X) 3) :=
    fun z hzB => (hfAt z (Metric.ball_subset_closedBall hzB)).contDiffWithinAt
  have hf1Smooth : ContDiff ℝ ∞ f1 := scalarFirstCoefficient_smooth ell
  obtain ⟨A,A1,hA,hA1,S,hS,hz,hz1,V,hV,h0V,hRep,hRep1⟩ :=
    exists_relative_dilation_pair_family f f1 hfOn hf1Smooth.contDiffOn
  let D : ℝ × X → Mat := fun p => A p-r • A1 p
  have hD : ContDiff ℝ ∞ D := hA.sub (hA1.const_smul r)
  have hzD : ∀ t z,z ∉ S → D (t,z) = 0 := by
    intro t z hzS
    simp only [D,hz t z hzS,hz1 t z hzS,smul_zero,sub_zero]
  have hPoint (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :
      ContDiffAt ℝ ∞ R z ∧ (∀ i j : I,|R z i j| ≤ Q*r^2) ∧
        ‖fderiv ℝ R z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ B*r^2 :=
    hC2 floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy z hzB
  have hRepD (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :
      D =ᶠ[𝓝 (0,z)] (fun p => (1:Mat)+relativeDilationFamily R p) := by
    filter_upwards [hRep 0 h0V z hzB,hRep1 0 h0V z hzB] with p hp hp1
    change A p-r • A1 p = _
    rw [hp,hp1]
    exact normalized_coefficient_dilation_residual d y p
  obtain ⟨bD,hbD,hzbD,hCurveD,hVD0,hDD0⟩ := commonSupport_dilation_generator_bounds D hD S hS hzD R (1:Mat) hRepD
    (fun z hzB => (hPoint z hzB).1) (Q*r^2) (B*r^2) (by positivity) (by positivity)
    (fun z hzB => (hPoint z (unitBall_subset_closedBall_two hzB)).2.2.1)
    (fun z hzB => (hPoint z (unitBall_subset_closedBall_two hzB)).2.2.2)
  have hRate : Q*r^2+B*r^2 = CQ*r^2 := by dsimp only [CQ];ring
  have hVD (z : X) (hzB : z ∈ (ballOpens:Set X)) : ‖bD z‖ ≤ CQ*r^2 := by
    rw [← hRate];exact hVD0 z hzB
  have hDD (z : X) (hzB : z ∈ (ballOpens:Set X)) : ‖fderiv ℝ bD z‖ ≤ CQ*r^2 := by
    rw [← hRate];exact hDD0 z hzB
  have hRep10 (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :
      A1 =ᶠ[𝓝 (0,z)] (fun p => (0:Mat)+relativeDilationFamily f1 p) := by
    simpa only [zero_add] using hRep1 0 h0V z hzB
  have hFirstBounds (z : X) := scalarFirstCoefficient_derivative_bounds ell C1 hC1 hEll z
  obtain ⟨b1,hb1,hzb1,hCurve1,hV10,hD10⟩ := commonSupport_dilation_generator_bounds A1 hA1 S hS hz1 f1 0 hRep10
    (fun _ _ => hf1Smooth.contDiffAt) C1 0 hC1 (by norm_num)
    (fun z _ => (hFirstBounds z).1) (fun z _ => by rw [(hFirstBounds z).2];simp)
  have hV1 (z : X) (hzB : z ∈ (ballOpens:Set X)) : ‖b1 z‖ ≤ C1 := by simpa only [add_zero] using hV10 z hzB
  have hD1 (z : X) (hzB : z ∈ (ballOpens:Set X)) : ‖fderiv ℝ b1 z‖ ≤ C1 := by simpa only [add_zero] using hD10 z hzB
  have hScalar (t : ℝ) (ht : t ∈ V) (w : UnitSphere) : A1 (t,w.val) = ((1+t) • ell) w.val • (1:Mat) := by
    have hw : w.val ∈ Metric.closedBall (0:X) 2 :=
      Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
    exact ((hRep1 t ht w.val hw).eq_of_nhds).trans (relativeDilation_scalarFirstCoefficient ell (t,w.val))
  exact ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hRep,hRep1,(fun _ => rfl),
    b1,hb1,hzb1,hCurve1,hV1,hD1,bD,hbD,hzbD,hCurveD,hVD,hDD,hScalar⟩

end ShrinkingSpheres
