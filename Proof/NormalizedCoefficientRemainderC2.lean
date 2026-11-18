import Proof.UniformFirstCoefficientRemainderC2
import Proof.NormalizedFirstCoefficientTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

def normalizedFirstCoefficientRemainder (d : Data) (y : X) : X → Mat :=
  affineMatrixRemainder (normalizedFirstNormalCoefficient d y) 1 (d.radius y) (firstDensityLogCovector d y)

lemma normalizedFirstCoefficientRemainder_eq (d : Data) (y : X) :
    normalizedFirstCoefficientRemainder d y = (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ •
      affineMatrixRemainder (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)))
        (firstMetricDensityFactor d.γ d.g₁ y) (d.radius y) (firstDensityCenterLinearL d y) := by
  have hc := (firstMetricDensityFactor_pos d.γ d.g₁ y).ne'
  funext z
  ext i j
  change (firstMetricDensityFactor d.γ d.g₁ y)⁻¹*_
    -(1+d.radius y*((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*firstDensityCenterLinearL d y z))*(1:Mat) i j = _
  simp only [Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,affineMatrixRemainder,Matrix.sub_apply]
  field_simp

/-- The same actual normalized remainder has a quadratic spatial C2 bound,
    transferred from the shared unnormalized Taylor producer. -/
theorem uniform_normalized_coefficient_remainder_C2 {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Q B : ℝ,0 < η ∧ 0 ≤ Q ∧ 0 ≤ B ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ z ∈ Metric.closedBall (0:X) 2,
      let R := normalizedFirstCoefficientRemainder d y
      ContDiffAt ℝ ∞ R z ∧ (∀ i j : I,|R z i j| ≤ Q*(d.radius y)^2) ∧
        ‖fderiv ℝ R z‖ ≤ Q*(d.radius y)^2 ∧ ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ B*(d.radius y)^2 := by
  obtain ⟨η,Q,B,hη,hQ,hB,hData⟩ := uniform_first_coefficient_remainder_C2 hY hΩ hm K ρ c₀ M Cj hK hρ
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨η,K*Q,K*B,hη,mul_nonneg hK0 hQ,mul_nonneg hK0 hB,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz
  obtain ⟨hR,hVal,hD,hD2⟩ := hData floor hf ε hε hSmall d hd y hy z hz
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let R0 := affineMatrixRemainder (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)))
    c (d.radius y) (firstDensityCenterLinearL d y)
  let R := normalizedFirstCoefficientRemainder d y
  have hEq : R = c⁻¹ • R0 := normalizedFirstCoefficientRemainder_eq d y
  have hci : |c⁻¹| ≤ K := by
    rw [abs_of_pos (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))]
    exact hd.1.firstMetricDensityFactor_inverse_le (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy)
  have hDFun : fderiv ℝ R = c⁻¹ • fderiv ℝ R0 := by
    rw [hEq]
    exact fderiv_const_smul_field c⁻¹
  have hDPoint : fderiv ℝ R z = c⁻¹ • fderiv ℝ R0 z := congrArg (fun D : X → X →L[ℝ] Mat => D z) hDFun
  have hD2Point : fderiv ℝ (fderiv ℝ R) z = c⁻¹ • fderiv ℝ (fderiv ℝ R0) z := by
    rw [hDFun]
    exact congrArg (fun D : X → X →L[ℝ] (X →L[ℝ] Mat) => D z)
      (fderiv_const_smul_field (f:=fderiv ℝ R0) c⁻¹)
  change ContDiffAt ℝ ∞ R z ∧ (∀ i j : I,|R z i j| ≤ (K*Q)*(d.radius y)^2) ∧
    ‖fderiv ℝ R z‖ ≤ (K*Q)*(d.radius y)^2 ∧ ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ (K*B)*(d.radius y)^2
  refine ⟨?_,?_,?_,?_⟩
  · rw [hEq]
    exact hR.const_smul (c⁻¹)
  · intro i j
    have hv : R z i j = c⁻¹*R0 z i j := congrArg (fun f : X → Mat => f z i j) hEq
    rw [hv,abs_mul]
    exact (mul_le_mul hci (hVal i j) (abs_nonneg _) hK0).trans_eq (by ring)
  · rw [hDPoint,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hci hD (norm_nonneg _) hK0).trans_eq (by ring)
  · rw [hD2Point,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hci hD2 (norm_nonneg _) hK0).trans_eq (by ring)

end ShrinkingSpheres
