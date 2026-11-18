import Proof.FirstMetricDensityFactor
import Proof.FramedNormalMetric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- Actual scalar conformal density expressed in the admitted normal chart. -/
def framedFirstDensityFactor (d : Data) (y z : X) : ℝ :=
  firstMetricDensityFactor d.γ d.g₁ (d.expMap (y,d.radius y • frameVector d.frame y z))

def firstDensityCenterLinearL (d : Data) (y : X) : X →L[ℝ] ℝ :=
  (fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) y).comp (frameVectorLinear d.frame y)

lemma Elliptic.norm_frameVectorLinear_le {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 1 ≤ K) {y : X} (hy : y ∈ Ω) (e : Frame)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    ‖frameVectorLinear e y‖ ≤ K := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  apply ContinuousLinearMap.opNorm_le_bound _ hKpos.le
  intro u
  rw [frameVectorLinear_apply]
  have hb := (hg.frameVector_norm_sq_bounds hKpos hy e he u).2
  have hKsq : K ≤ K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hKpos.le (norm_nonneg u))).mp
  have hMul := mul_le_mul_of_nonneg_right hKsq (sq_nonneg ‖u‖)
  nlinarith only [hb,hMul]

/-- Exact scalar conformal factorization of the actual two normal metric fields. -/
theorem Admissible.framed_firstMetric_density_metric {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y z : X}
    (hx : d.expMap (y,d.radius y • frameVector d.frame y z) ∈ Ω) :
    framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y) z =
      (framedFirstDensityFactor d y z)^2 • framedNormalMetric d.γ d.frame d.expMap y (d.radius y) z := by
  ext i j
  change metricPair d.g₁ _ _ _ = _
  rw [hd.1.firstMetricPair_eq_conformalFactor hK hx,
    ← hd.1.firstMetricDensityFactor_sq hK hx]
  rfl

/-- Exact dimension-three factorization of the actual normal divergence coefficients. -/
theorem Admissible.framed_firstMetric_density_coefficient {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y z : X}
    (hx : d.expMap (y,d.radius y • frameVector d.frame y z) ∈ Ω)
    (hDet : IsUnit (framedNormalMetric d.γ d.frame d.expMap y (d.radius y) z).det) :
    principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z =
      framedFirstDensityFactor d y z •
        principalCoefficient (framedNormalMetric d.γ d.frame d.expMap y (d.radius y)) z := by
  have hp : 0 < framedFirstDensityFactor d y z := firstMetricDensityFactor_pos _ _ _
  have hScale := principalCoefficient_radius_sq
    (framedNormalMetric d.γ d.frame d.expMap y (d.radius y)) (framedFirstDensityFactor d y z) hp z hDet
  exact (show principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z =
      principalCoefficient (fun w => (framedFirstDensityFactor d y z)^2 •
        framedNormalMetric d.γ d.frame d.expMap y (d.radius y) w) z by
      simp only [principalCoefficient,OAI.AnisotropicCalderon.vol,
        hd.framed_firstMetric_density_metric hK hx]).trans hScale

end ShrinkingSpheres
