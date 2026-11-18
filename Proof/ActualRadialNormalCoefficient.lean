import Proof.FramedNormalRadialCoefficient
import Proof.RelativeRadiusCoefficientModel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

def actualRadialNormalCoefficient (d : Data) (y z : X) : ℝ :=
  (firstMetricDensityFactor d.γ d.g₁ y)⁻¹*framedFirstDensityFactor d y z*
    Real.sqrt (framedNormalMetric d.γ d.frame d.expMap y (d.radius y) z).det

lemma Admissible.normalizedFirstNormalCoefficient_radial_row {Y Ω : Set X}
    (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ}
    {Cj : Fin 9 → ℝ} {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hK : 0 < K) {y : X} (hy : y ∈ Y) (z : X)
    (hv : d.radius y • frameVector d.frame y z ∈ interior (disk d.γ y (max ρ (d.radius y))))
    (hDet : IsUnit (framedNormalMetric d.γ d.frame d.expMap y (d.radius y) z).det) (j : I) :
    ∑ i : I,z i*normalizedFirstNormalCoefficient d y z i j=actualRadialNormalCoefficient d y z*z j := by
  have hyΩ := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hx := hd.2.1.path_image hy (d.radius y • frameVector d.frame y z) (interior_subset hv)
    (by constructor <;> norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1)
  simp only [one_smul] at hx
  have hFactor := hd.framed_firstMetric_density_coefficient hK hx hDet
  have hRad := hd.2.1.framedNormal_principal_radial_row hΩ hd.1.1 hK hy hyΩ d.frame hFrame
    (d.radius y) hr z hv hDet j
  calc
    _ = ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*framedFirstDensityFactor d y z)*
      (∑ i : I,z i*principalCoefficient (framedNormalMetric d.γ d.frame d.expMap y (d.radius y)) z i j) := by
      simp only [normalizedFirstNormalCoefficient,firstNormalCoefficientAtRadius,hFactor,
        Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := (congrArg (fun q : ℝ =>
      ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*framedFirstDensityFactor d y z)*q) hRad).trans (by
        unfold actualRadialNormalCoefficient
        ring)
end ShrinkingSpheres
