import Proof.OrthonormalCoefficientSmoothDomain
import Proof.NormalFrameSignedRadiusControl
import Proof.PullbackMatrixPointEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- Shared producer of true smooth neighborhoods along the entire signed
    radial segment of the genuine orthonormal coefficient family. -/
theorem uniform_orthonormal_coefficient_smooth_domains {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η : ℝ,0 < η ∧ η ≤ 1 ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ t : ℝ,|t| ≤ d.radius y →
      ∃ U : Set (NormalFrameParameter × X),IsOpen U ∧ ((y,(t,L)),z) ∈ U ∧
        ContDiffOn ℝ ∞ (orthonormalNormalFrameCoefficient d.γ d.g₁ d.expMap) U := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨η,hη,hη1,hGeometry⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ
    hm K ρ c₀ M Cj hK hρ Z hZ
  refine ⟨η,hη,hη1,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz t ht
  have hCenter := hd.2.1.center_mem hy
  have hPack := hGeometry floor hf ε hε hSmall d hd y hy L he t ht z hz
  have hPoint : ‖normalFrameMetric d.g₁ d.expMap ((y,(t,L)),z)‖ ≤ 4*K^2 ∧
      (((metricDensityBudget (4*K^2))⁻¹)^2) ≤ (normalFrameMetric d.g₁ d.expMap ((y,(t,L)),z)).det := by
    rw [normalFrameMetric_eq_universal_pullback]
    exact hd.1.1.universalPullbackMetricMatrix_point_bounds hd.1.2.1 hKpos y
      (d.expMap (y,t • L z)) hCenter hPack.2.1
      (normalVerticalJacobian d.expMap y (t • L z)) L he hPack.2.2.2.1
  have hPos : 0 < (normalFrameMetric d.g₁ d.expMap ((y,(t,L)),z)).det :=
    (show 0 < (((metricDensityBudget (4*K^2))⁻¹)^2) by unfold metricDensityBudget;positivity).trans_le hPoint.2
  exact hd.1.exists_orthonormalFrame_coefficient_domain hΩ hKpos hd.2.1 hy t L z he hPack.1.1.le hPos

end ShrinkingSpheres
