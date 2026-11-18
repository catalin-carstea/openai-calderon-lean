import Proof.UniformFirstCoefficientTaylor
import Proof.CanonicalFirstRadialCorrection

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

def normalizedFirstNormalCoefficient (d : Data) (y z : X) : Mat :=
  (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ •
    principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z

/-- Normalizing by the center scalar fixes the flat base coefficient at
    identity. The same quadratic C1 remainder uses the canonical log covector. -/
theorem uniform_normalized_first_coefficient_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η Q : ℝ,0 < η ∧ 0 ≤ Q ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      let A := normalizedFirstNormalCoefficient d y
      let q := firstDensityLogCovector d y
      |A z i j-(1+d.radius y*q z)*(1:Mat) i j| ≤ Q*(d.radius y)^2 ∧
      ‖fderiv ℝ (fun w => A w i j) z-(d.radius y*(1:Mat) i j) • q‖ ≤ Q*(d.radius y)^2 := by
  have hProducer := uniform_first_coefficient_taylor (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ L hL
  obtain ⟨η,Q,hη,hQ,hData⟩ := hProducer
  refine ⟨η,K*Q,hη,mul_nonneg (zero_lt_one.trans_le hK).le hQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz i j
  have hPoint := hData floor hf ε hε hSmall d hd y hy z hz i j
  let A := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ell := firstDensityCenterLinearL d y
  let r := d.radius y
  have hc : c ≠ 0 := (firstMetricDensityFactor_pos _ _ _).ne'
  have hci : |c⁻¹| ≤ K := by
    rw [abs_of_pos (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))]
    exact hd.1.firstMetricDensityFactor_inverse_le (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy)
  have hValue : normalizedFirstNormalCoefficient d y z i j-(1+r*firstDensityLogCovector d y z)*(1:Mat) i j =
      c⁻¹*(A z i j-(c+r*ell z)*(1:Mat) i j) := by
    change c⁻¹*A z i j-(1+r*(c⁻¹*ell z))*(1:Mat) i j = _
    field_simp
  have hFD : fderiv ℝ (fun w => normalizedFirstNormalCoefficient d y w i j) z =
      c⁻¹ • fderiv ℝ (fun w => A w i j) z := by
    change fderiv ℝ (c⁻¹ • fun w => A w i j) z = _
    exact congrArg (fun D : X → X →L[ℝ] ℝ => D z) (fderiv_const_smul_field c⁻¹)
  have hDerivative : fderiv ℝ (fun w => normalizedFirstNormalCoefficient d y w i j) z-
      (r*(1:Mat) i j) • firstDensityLogCovector d y =
      c⁻¹ • (fderiv ℝ (fun w => A w i j) z-(r*(1:Mat) i j) • ell) := by
    rw [hFD]
    change c⁻¹ • fderiv ℝ (fun w => A w i j) z-(r*(1:Mat) i j) • (c⁻¹ • ell) = _
    module
  refine ⟨?_,?_⟩
  · rw [hValue,abs_mul]
    exact (mul_le_mul hci hPoint.1 (abs_nonneg _) (zero_lt_one.trans_le hK).le).trans_eq (by ring)
  · rw [hDerivative,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hci hPoint.2 (norm_nonneg _) (zero_lt_one.trans_le hK).le).trans_eq (by ring)

end ShrinkingSpheres
