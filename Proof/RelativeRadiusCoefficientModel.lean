import Proof.NormalizedCoefficientRemainderC2
import Proof.RelativeDilationPairFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

def firstNormalCoefficientAtRadius (d : Data) (y : X) (r : ℝ) (z : X) : Mat :=
  (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ • principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) z

lemma framedNormalMetric_radius_mul (g : MetricField) (e : Frame) (E : X × X → X)
    (y z : X) (r s : ℝ) :
    framedNormalMetric g e E y (r*s) z = framedNormalMetric g e E y r (s • z) := by
  have hFrame : frameVector e y (s • z) = s • frameVector e y z := by
    rw [← frameVectorLinear_apply,← frameVectorLinear_apply,map_smul]
  ext i j
  simp only [framedNormalMetric,normalPullbackMetricPair,hFrame,smul_smul]

lemma relativeDilation_normalized_coefficient (d : Data) (y : X) (p : ℝ × X) :
    relativeDilationFamily (normalizedFirstNormalCoefficient d y) p =
      firstNormalCoefficientAtRadius d y (d.radius y*(1+p.1)) p.2 := by
  unfold relativeDilationFamily normalizedFirstNormalCoefficient firstNormalCoefficientAtRadius
  have hField : framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y*(1+p.1)) =
      (fun z => framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y) ((1+p.1) • z)) :=
    funext (fun z => framedNormalMetric_radius_mul d.g₁ d.frame d.expMap y z (d.radius y) (1+p.1))
  rw [hField]
  rfl

def scalarFirstCoefficient (ell : X →L[ℝ] ℝ) : X → Mat := ell.smulRight (1:Mat)

lemma scalarFirstCoefficient_apply (ell : X →L[ℝ] ℝ) (z : X) :
    scalarFirstCoefficient ell z = ell z • (1:Mat) := rfl

lemma scalarFirstCoefficient_smooth (ell : X →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (scalarFirstCoefficient ell) := (ell.smulRight (1:Mat)).contDiff

lemma scalarFirstCoefficient_derivative_bounds (ell : X →L[ℝ] ℝ) (P : ℝ) (hP : 0 ≤ P)
    (hEll : ‖ell‖ ≤ P) (z : X) :
    ‖fderiv ℝ (scalarFirstCoefficient ell) z‖ ≤ P ∧
      fderiv ℝ (fderiv ℝ (scalarFirstCoefficient ell)) z = 0 := by
  have hNormOne : ‖(1:Mat)‖ ≤ 1 := by
    apply (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hFD : fderiv ℝ (scalarFirstCoefficient ell) = fun _ : X => ell.smulRight (1:Mat) := by
    funext w
    exact (ell.smulRight (1:Mat)).fderiv
  constructor
  · rw [hFD]
    exact ((ell.norm_smulRight_apply (1:Mat)).le).trans
      ((mul_le_mul hEll hNormOne (norm_nonneg _) hP).trans_eq (mul_one P))
  · rw [hFD]
    exact fderiv_const_apply _

lemma relativeDilation_scalarFirstCoefficient (ell : X →L[ℝ] ℝ) (p : ℝ × X) :
    relativeDilationFamily (scalarFirstCoefficient ell) p = ((1+p.1) • ell) p.2 • (1:Mat) := by
  simp only [relativeDilationFamily,scalarFirstCoefficient_apply,map_smul,_root_.smul_apply,smul_eq_mul]

lemma normalized_coefficient_dilation_residual (d : Data) (y : X) (p : ℝ × X) :
    relativeDilationFamily (normalizedFirstNormalCoefficient d y) p-
      d.radius y • relativeDilationFamily (scalarFirstCoefficient (firstDensityLogCovector d y)) p =
        (1:Mat)+relativeDilationFamily (normalizedFirstCoefficientRemainder d y) p := by
  simp only [relativeDilationFamily,normalizedFirstCoefficientRemainder,affineMatrixRemainder,
    scalarFirstCoefficient_apply,add_smul,one_smul]
  module

end ShrinkingSpheres
