import Proof.NormalFrameFirstCovectorRegularity
import Proof.RadialCorrectionLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

/-- The true first-correction remainder on the full independent geometric
    parameter space. The first covector and radius are shared with the PDE. -/
def normalFrameRadialTaylorFamily (d : Data)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (p : NormalFrameParameter) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  R p-p.2.1 • (radialCorrectionCovectorL (normalFrameFirstCovector d.γ d.g₁ p)).comp
    (sphereSobolevInclusionL 1 0 (by norm_num))

lemma normalFrameRadialTaylorFamily_parallel (d : Data)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (y a : X) (t : ℝ) :
    normalFrameRadialTaylorFamily d R (normalFrameParallelCurve d.γ d.frame d.radius y a t) =
      R (normalFrameParallelCurve d.γ d.frame d.radius y a t)-d.radius y •
        (coarseFirstRadialVariationL 1 (parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) t)).comp
          (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  unfold normalFrameRadialTaylorFamily
  rw [normalFrameFirstCovector_parallel,radialCorrectionCovectorL_apply]
  rfl

lemma Background.normalFrameFirstCovector_actual {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω) :
    normalFrameFirstCovector d.γ d.g₁ (y,(d.radius y,frameVectorLinear d.frame y)) = firstDensityLogCovector d y :=
  (h.firstDensityLogCovector_eq_differential hK hΩ hy).symm

lemma Background.normalFrameRadialTaylorFamily_actual {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    normalFrameRadialTaylorFamily d R (y,(d.radius y,frameVectorLinear d.frame y)) =
      R (y,(d.radius y,frameVectorLinear d.frame y))-d.radius y •
        (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  unfold normalFrameRadialTaylorFamily
  rw [h.normalFrameFirstCovector_actual hΩ hK hy,← firstRadialCorrectionL_eq_covector]

lemma Background.normalFrameRadialTaylorFamily_radius {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (t : ℝ) :
    normalFrameRadialTaylorFamily d R (normalFrameRadiusCurve d.frame d.radius y t) =
      R (normalFrameRadiusCurve d.frame d.radius y t)-d.radius y •
        (coarseFirstRadialVariationL 1 ((1+t) • firstDensityLogCovector d y)).comp
          (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have hCov : normalFrameFirstCovector d.γ d.g₁ (normalFrameRadiusCurve d.frame d.radius y t) = firstDensityLogCovector d y :=
    h.normalFrameFirstCovector_actual hΩ hK hy
  unfold normalFrameRadialTaylorFamily
  rw [hCov,← radialCorrectionCovectorL_apply,map_smul,ContinuousLinearMap.smul_comp,smul_smul]
  congr 1
  change ((1+t)*d.radius y) • _ = (d.radius y*(1+t)) • _
  rw [mul_comm]

lemma Background.normalFrameFirstCovector_rotation {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (i j : I) (t : ℝ) :
    normalFrameFirstCovector d.γ d.g₁ (normalFrameRotationCurve d.frame d.radius y i j t) =
      (firstDensityLogCovector d y).comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [h.firstDensityLogCovector_eq_differential hK hΩ hy]
  rfl

lemma Background.normalFrameRadialTaylorFamily_rotation {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i j : I) (t : ℝ) :
    normalFrameRadialTaylorFamily d R (normalFrameRotationCurve d.frame d.radius y i j t) =
      R (normalFrameRotationCurve d.frame d.radius y i j t)-d.radius y •
        (coarseFirstRadialVariationL 1 ((firstDensityLogCovector d y).comp
          (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).comp
            (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  unfold normalFrameRadialTaylorFamily
  rw [h.normalFrameFirstCovector_rotation hΩ hK hy,radialCorrectionCovectorL_apply]
  rfl

/-- The first-correction subtraction is smooth on the same actual geometric
    neighborhood as the midpoint family. -/
theorem Background.contDiffOn_normalFrameRadialTaylorFamily {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (V : Set NormalFrameParameter)
    (hR : ContDiffOn ℝ ∞ R V) (hCenter : ∀ p ∈ V,p.1 ∈ Ω) :
    ContDiffOn ℝ ∞ (normalFrameRadialTaylorFamily d R) V := by
  have hQ := h.contDiffOn_normalFrameFirstCovector hΩ hK V hCenter
  have hB := (radialCorrectionCovectorL.contDiff.comp_contDiffOn hQ).clm_comp
    (contDiffOn_const (c:=sphereSobolevInclusionL 1 0 (by norm_num)))
  exact hR.sub (contDiffOn_snd.fst.smul hB)

end ShrinkingSpheres
