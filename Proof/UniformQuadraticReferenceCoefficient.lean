import Proof.UniformQuadraticReferenceMetric
import Proof.UniformNormalCoefficientCloseness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

def normalReferenceCoefficientClosenessBudget {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (L : ℝ) : ℝ :=
  metricDensityBudget (4*K^2)*(9*(4*K^2)^2+18*(4*K^2)^3)*normalReferenceMetricClosenessBudget hm K M L

/-- The actual reference divergence coefficient is quadratically close to the
    Euclidean coefficient on every fixed enlarged normal ball. -/
theorem uniform_framed_reference_coefficient_quadratic {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      |principalCoefficient (framedNormalMetric d.γ d.frame d.expMap y (d.radius y)) z i j-(1:Mat) i j| ≤
        normalReferenceCoefficientClosenessBudget hm K M L*(d.radius y)^2 := by
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ L hL
  obtain ⟨ηM,hηM,hClose⟩ := uniform_framed_reference_metric_quadratic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨min ηE ηM,lt_min hηE hηM,?_⟩
  intro floor hf ε hε hSmall d hd y hy z hz i j
  let H := framedNormalMetric d.γ d.frame d.expMap y (d.radius y)
  have hEll : Elliptic (Metric.closedBall (0:X) L) (4*K^2) H :=
    hE floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy d.γ (by simp)
  have h0 : (0:X) ∈ Metric.closedBall (0:X) L := by simpa only [Metric.mem_closedBall,dist_self] using hL
  have hframe := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hCenter : H 0 = (1:Mat) := by
    ext a b
    change framedNormalMetric d.γ d.frame d.expMap y (d.radius y) 0 a b = (1:Mat) a b
    rw [hd.2.1.framedNormalMetric_center hy d.γ d.frame hframe,hframe]
    rfl
  have hP0 : principalCoefficient H 0 = (1:Mat) := by
    simp only [principalCoefficient,OAI.AnisotropicCalderon.vol,hCenter,Matrix.det_one,Real.sqrt_one,inv_one,one_smul]
  have hDiff (a b : I) : |H z a b-H 0 a b| ≤ normalReferenceMetricClosenessBudget hm K M L*(d.radius y)^2 := by
    rw [hCenter]
    exact hClose floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy z hz a b
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hConst : 0 < 4*K^2 := by positivity
  have hGeom : 0 ≤ normalReferenceMetricClosenessBudget hm K M L := by
    dsimp [normalReferenceMetricClosenessBudget,normalReferenceMetricSecondBudget,
      normalVelocitySecondErrorBudget,normalVariationErrorBudget,backgroundConnectionDerivativeBudget]
    positivity
  have hb := hEll.principalCoefficient_difference_bound hEll hConst hz h0
    (normalReferenceMetricClosenessBudget hm K M L*(d.radius y)^2)
    (mul_nonneg hGeom (sq_nonneg _)) hDiff i j
  rw [hP0] at hb
  exact hb.trans_eq (by dsimp only [normalReferenceCoefficientClosenessBudget];ring)

end ShrinkingSpheres
