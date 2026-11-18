import Proof.FirstMetricDensityFactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 15
open Set
namespace ShrinkingSpheres

/-- Ellipticity bounds the reciprocal canonical density factor as well. -/
theorem Background.firstMetricDensityFactor_inverse_le {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    (firstMetricDensityFactor γ g₁ x)⁻¹ ≤ K := by
  have hl := ((hB.2.1.2 x hx).2 (axis 0)).1
  have hu := ((hB.1.2 x hx).2 (axis 0)).2
  have hEntry (g : MetricField) : metricPair g x (axis 0) (axis 0) = g x 0 0 := by simp [metricPair,axis]
  rw [hEntry,norm_axis,one_pow,mul_one] at hl hu
  have hMul := mul_le_mul_of_nonneg_left hl (sq_nonneg K)
  have hCancel : K^2*K⁻¹ = K := by field_simp
  rw [hCancel] at hMul
  have hRatio : γ x 0 0/g₁ x 0 0 ≤ K^2 :=
    (div_le_iff₀ (hB.2.1.diagonal_entry_pos hK hx 0)).mpr (hu.trans (by nlinarith only [hMul]))
  have hInvSq : ((firstMetricDensityFactor γ g₁ x)⁻¹)^2 = γ x 0 0/g₁ x 0 0 := by
    rw [inv_pow,hB.firstMetricDensityFactor_sq hK hx,firstMetricConformalFactor,inv_div]
  rw [← hInvSq] at hRatio
  exact (sq_le_sq₀ (inv_nonneg.mpr (firstMetricDensityFactor_pos γ g₁ x).le) hK.le).mp hRatio

lemma Background.firstMetricDensityFactor_mem_Icc {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    firstMetricDensityFactor γ g₁ x ∈ Icc K⁻¹ K := by
  refine ⟨?_,hB.firstMetricDensityFactor_le hK hx⟩
  have hMul := (inv_le_iff_one_le_mul₀ (firstMetricDensityFactor_pos γ g₁ x)).mp
    (hB.firstMetricDensityFactor_inverse_le hK hx)
  apply (inv_le_iff_one_le_mul₀ hK).mpr
  nlinarith only [hMul]

end ShrinkingSpheres
