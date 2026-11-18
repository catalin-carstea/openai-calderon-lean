import Proof.RadialCorrectionLinear
import Proof.FirstMetricNormalDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def firstDensityLogCovector (d : Data) (y : X) : X →L[ℝ] ℝ :=
  (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ • firstDensityCenterLinearL d y

/-- The canonical pointwise correction used by the actual radial Taylor proof. -/
def firstRadialCorrectionL (d : Data) (y : X) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  coarseFirstRadialVariationL (firstMetricDensityFactor d.γ d.g₁ y) (firstDensityCenterLinearL d y)

theorem firstRadialCorrectionL_eq_covector (d : Data) (y : X) :
    firstRadialCorrectionL d y = radialCorrectionCovectorL (firstDensityLogCovector d y) :=
  coarseFirstRadialVariationL_normalized_covector _ _

/-- The normalized density gradient is minus the conformal-depth gradient.
    This removes the exponential scalar from the correction's derivative estimates. -/
theorem Background.firstDensityLogCovector_eq_depth {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω) :
    firstDensityLogCovector d y =
      -(fderiv ℝ (firstMetricConformalDepth d.γ d.g₁) y).comp (frameVectorLinear d.frame y) := by
  let t := firstMetricConformalDepth d.γ d.g₁
  let c := firstMetricDensityFactor d.γ d.g₁ y
  have ht := (hB.firstMetricConformalDepth_smooth hK).contDiffAt (hΩ.mem_nhds hy)
  have hD : fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) y = c • (-fderiv ℝ t y) :=
    ((ht.differentiableAt (by simp)).hasFDerivAt.neg.exp).fderiv
  have hc : c ≠ 0 := (firstMetricDensityFactor_pos d.γ d.g₁ y).ne'
  apply ContinuousLinearMap.ext
  intro z
  change c⁻¹*(fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) y (frameVectorLinear d.frame y z)) =
    -(fderiv ℝ t y (frameVectorLinear d.frame y z))
  rw [hD,_root_.smul_apply,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  rfl

theorem Background.norm_firstDensityLogCovector_le {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) :
    ‖firstDensityLogCovector d y‖ ≤ K^2*|M ⟨1,by omega⟩| := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  rw [hB.firstDensityLogCovector_eq_depth hΩ hKpos hy,norm_neg]
  have hT := (hB.firstMetricConformalDepth_jet_bounds hΩ hKpos hm hy).1
  have hE := hB.1.norm_frameVectorLinear_le hK hy d.frame (hB.2.2.2.2.2.2.2 y hy)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hT hE (norm_nonneg _) (by positivity)).trans_eq (by ring))

theorem Background.norm_firstRadialCorrectionL_le {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) :
    ‖firstRadialCorrectionL d y‖ ≤ 6*K^2*|M ⟨1,by omega⟩| := by
  rw [firstRadialCorrectionL_eq_covector]
  exact (norm_radialCorrectionCovectorL_apply_le _).trans
    ((mul_le_mul_of_nonneg_left (hB.norm_firstDensityLogCovector_le hΩ hK hm hy) (by norm_num : (0:ℝ) ≤ 6)).trans_eq (by ring))

end ShrinkingSpheres
