import Proof.AffineMatrixRemainderJets
import Proof.UniformFirstCoefficientTaylor
import Proof.UniformNormalCoefficientSecondDerivative
import Proof.JointMetricCoefficientRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Shared actual coefficient remainder C2 data. Its spatial first and second
    derivatives are uniformly quadratic in the admitted radius. -/
theorem uniform_first_coefficient_remainder_C2 {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Q B : ℝ,0 < η ∧ 0 ≤ Q ∧ 0 ≤ B ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ z ∈ Metric.closedBall (0:X) 2,
      let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let R := affineMatrixRemainder a (firstMetricDensityFactor d.γ d.g₁ y) (d.radius y) (firstDensityCenterLinearL d y)
      ContDiffAt ℝ ∞ R z ∧ (∀ k l : I,|R z k l| ≤ Q*(d.radius y)^2) ∧
        ‖fderiv ℝ R z‖ ≤ Q*(d.radius y)^2 ∧ ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ B*(d.radius y)^2 := by
  obtain ⟨ηT,Q,hηT,hQ,hTaylor⟩ := uniform_first_coefficient_taylor
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨η2,hη2,hSecond⟩ := uniform_framed_normal_coefficient_second_derivative hY hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηS,hηS,hSmooth⟩ := uniform_framed_normal_coefficient_joint_regular hY hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let B := |normalCoefficientAngularSecondDerivativeBudget hm K M|
  have hB : 0 ≤ B := abs_nonneg _
  refine ⟨min ηT (min η2 ηS),Q,B,lt_min hηT (lt_min hη2 hηS),hQ,hB,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz
  dsimp only
  have hST := hSmall.trans (min_le_left _ _)
  have hS2 := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSS := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  let R := affineMatrixRemainder a c r ell
  have ha : ContDiffAt ℝ ∞ a z := by
    apply contDiffAt_pi.mpr
    intro k
    apply contDiffAt_pi.mpr
    intro l
    have hJoint := hSmooth floor hf ε hε hSS d hd y hy d.g₁ (by simp) z hz k l
    simpa only [Function.comp_def] using hJoint.comp z (contDiffAt_const.prodMk contDiffAt_id)
  have hR : ContDiffAt ℝ ∞ R z := contDiffAt_affineMatrixRemainder a c r ell z ha
  have hValue (k l : I) : |R z k l| ≤ Q*r^2 := (hTaylor floor hf ε hε hST d hd y hy z hz k l).1
  have hFirst : ‖fderiv ℝ R z‖ ≤ Q*r^2 := by
    apply norm_fderiv_matrix_le_of_entries R z (hR.differentiableAt (by simp)) _ (by positivity)
    intro k l
    change ‖fderiv ℝ (fun w => affineMatrixRemainder a c r ell w k l) z‖ ≤ _
    rw [fderiv_affineMatrixRemainder_entry a c r ell z (ha.differentiableAt (by simp)) k l]
    exact (hTaylor floor hf ε hε hST d hd y hy z hz k l).2
  have hSecondR : ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ B*r^2 := by
    apply norm_second_fderiv_matrix_le_of_entries R z hR _ (by positivity)
    intro k l
    change ‖fderiv ℝ (fderiv ℝ (fun w => affineMatrixRemainder a c r ell w k l)) z‖ ≤ _
    rw [second_fderiv_affineMatrixRemainder_entry a c r ell z ha k l]
    exact (hSecond floor hf ε hε hS2 d hd y hy d.g₁ (by simp) z hz k l).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r))
  exact ⟨hR,hValue,hFirst,hSecondR⟩

end ShrinkingSpheres
