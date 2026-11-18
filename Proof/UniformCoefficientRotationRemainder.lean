import Proof.UniformFirstCoefficientRemainderC2
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

def firstCoefficientRemainder (d : Data) (y : X) : X → Mat :=
  affineMatrixRemainder (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)))
    (firstMetricDensityFactor d.γ d.g₁ y) (d.radius y) (firstDensityCenterLinearL d y)

/-- The true quadratic normal coefficient remainder has a uniformly
    quadratic angular derivative with a uniformly quadratic spatial first jet.
    Every admitted radius and arbitrary smooth orthonormal frame is allowed. -/
theorem uniform_first_coefficient_rotation_remainder_C1 {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      ∀ z ∈ Metric.closedBall (0:X) 2,
        HasDerivAt (fun t : ℝ => coordinateRotationPrincipalFamily i j
          (fun q : ℝ × X => firstCoefficientRemainder d y q.2) ((t,0),z))
            (rotationPrincipalCoefficientDerivative i j (firstCoefficientRemainder d y) z) 0 ∧
        ‖rotationPrincipalCoefficientDerivative i j (firstCoefficientRemainder d y) z‖ ≤ C*(d.radius y)^2 ∧
        ‖fderiv ℝ (rotationPrincipalCoefficientDerivative i j (firstCoefficientRemainder d y)) z‖ ≤ C*(d.radius y)^2 := by
  obtain ⟨η,Q,B,hη,hQ,hB,hData⟩ := uniform_first_coefficient_remainder_C2 hY hΩ hm K ρ c₀ M Cj hK hρ
  let C := 30*Q+4*B
  refine ⟨η,C,hη,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j z hz
  let r := d.radius y
  let R := firstCoefficientRemainder d y
  obtain ⟨hR,hValue,hFirst,hSecondR⟩ := hData floor hf ε hε hSmall d hd y hy z hz
  have hzNorm : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  have hRD : DifferentiableAt ℝ R z := hR.differentiableAt (by simp)
  have hRDa : DifferentiableAt ℝ (fderiv ℝ R) z :=
    (hR.fderiv_right (m:=1) (by simp)).differentiableAt (by norm_num)
  refine ⟨hasDerivAt_coordinateRotationPrincipal_zero i j R z hRD,?_,?_⟩
  · apply (Matrix.norm_le_iff (by positivity : 0 ≤ C*r^2)).mpr
    intro k l
    have hAt := rotationPrincipalCoefficientDerivative_entry_bound i j R z (Q*r^2) (Q*r^2)
      (by positivity) (by positivity) hValue hFirst k l
    have hBound : 12*(Q*r^2)+2*(Q*r^2)*‖z‖ ≤ (16*Q)*r^2 := by
      have hzMul := mul_le_mul_of_nonneg_left hzNorm (by positivity : 0 ≤ 2*(Q*r^2))
      nlinarith only [hzMul]
    exact hAt.trans (hBound.trans (mul_le_mul_of_nonneg_right (by dsimp [C];linarith) (sq_nonneg r)))
  · have hAt := norm_fderiv_rotationPrincipalCoefficientDerivative_le i j R z hRD hRDa
      (Q*r^2) (B*r^2) (by positivity) (by positivity) hFirst hSecondR
    have hBound : 14*(Q*r^2)+2*(B*r^2)*‖z‖ ≤ (14*Q+4*B)*r^2 := by
      have hzMul := mul_le_mul_of_nonneg_left hzNorm (by positivity : 0 ≤ 2*(B*r^2))
      nlinarith only [hzMul]
    exact hAt.trans (hBound.trans (mul_le_mul_of_nonneg_right (by dsimp [C];linarith) (sq_nonneg r)))

end ShrinkingSpheres
