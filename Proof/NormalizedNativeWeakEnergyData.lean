import Proof.UniformEllipticWeakEstimates
import Proof.NativeWeakEnergyData
import Proof.PositiveCoefficientScaling
import Proof.NormalizedFirstCoefficientTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Every measurable representative of the actual normalized coefficient
    inherits uniform native weak coercivity, inverse and energy bounds. -/
theorem uniform_normalized_native_weak_energy_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ a : X → Mat,AEStronglyMeasurable a ((volume:Measure X).restrict ballOpens) →
      (∀ z ∈ (ballOpens:Set X),a z = normalizedFirstNormalCoefficient d y z) →
      NativeWeakEnergyData a (5*K*metricDensityBudget (4*K^2)*(4*K^2)) (K*metricDensityBudget (4*K^2)*(4*K^2)) := by
  obtain ⟨η,hη,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy a hMeas hEq
  let KP := 4*K^2
  let B := metricDensityBudget KP
  let c := firstMetricDensityFactor d.γ d.g₁ y
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith [sq_nonneg (K-1)]
  have hKP0 : 0 ≤ KP := zero_le_one.trans hKP
  have hB : 0 ≤ B := by dsimp [B,metricDensityBudget];positivity
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hcK : c ≤ K := hd.1.firstMetricDensityFactor_le hKpos (hd.2.1.center_mem hy)
  have hciK : c⁻¹ ≤ K := hd.1.firstMetricDensityFactor_inverse_le hKpos (hd.2.1.center_mem hy)
  have hEll := hElliptic floor hf ε hε hSmall d hd y hy d.g₁ (by simp)
  have hUE := (hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two
  have hScaled := uniformlyEllipticOn_positive_const_smul hUE c⁻¹ (inv_pos.mpr hc)
  have hActual : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) a (c⁻¹*(B⁻¹*KP⁻¹)) (c⁻¹*(B*KP)) := by
    apply hScaled.congr
    intro z hz
    exact hEq z hz
  obtain ⟨hcoeff,hCoercive,hInv,hEnergy⟩ := exists_native_weak_estimates_of_uniformlyElliptic a _ _ hActual hMeas
  have hInvScalar : 5*(c⁻¹*(B⁻¹*KP⁻¹))⁻¹ = 5*c*B*KP := by field_simp
  rw [hInvScalar] at hInv
  refine ⟨hcoeff,hCoercive,?_,?_⟩
  · exact hInv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcK (by norm_num)) hB) hKP0)
  · exact hEnergy.trans ((mul_le_mul_of_nonneg_right hciK (mul_nonneg hB hKP0)).trans_eq (by ring))

end ShrinkingSpheres
