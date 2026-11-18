import Proof.NormalFrameFirstCovectorRegularity
import Proof.NormalFrameRadialTaylorModel
import Proof.FlatDegreeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local irreducible] sphereSobolevDegreeL

def normalFrameRadialAdjointTaylorFamily (d : Data)
    (Da : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (p : NormalFrameParameter) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  Da p-sphereSobolevDegreeL-p.2.1 •
    (radialCorrectionCovectorL (normalFrameFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num))

lemma Background.normalFrameRadialAdjointTaylorFamily_actual {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (Da : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    normalFrameRadialAdjointTaylorFamily d Da (y,(d.radius y,frameVectorLinear d.frame y)) =
      Da (y,(d.radius y,frameVectorLinear d.frame y))-sphereSobolevDegreeL-d.radius y •
        (firstRadialCorrectionL d y).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have hB : radialCorrectionCovectorL
      (normalFrameFirstCovector d.γ d.g₁ (y,(d.radius y,frameVectorLinear d.frame y))) =
      firstRadialCorrectionL d y := by
    rw [h.normalFrameFirstCovector_actual hΩ hK hy,← firstRadialCorrectionL_eq_covector]
  exact congrArg (fun B : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    Da (y,(d.radius y,frameVectorLinear d.frame y))-sphereSobolevDegreeL-d.radius y •
      B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) hB

/-- Only the bounded L2 first correction is passed through abstract Hilbert
    adjunction. The full H1-to-L2 adjoint family is supplied separately. -/
theorem Background.contDiffOn_normalFrameRadialAdjointTaylorFamily {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (Da : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (V : Set NormalFrameParameter)
    (hDa : ContDiffOn ℝ ∞ Da V) (hCenter : ∀ p ∈ V,p.1 ∈ Ω) :
    ContDiffOn ℝ ∞ (normalFrameRadialAdjointTaylorFamily d Da) V := by
  let J : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
  have hQ := h.contDiffOn_normalFrameFirstCovector hΩ hK V hCenter
  have hB := (J.contDiff.comp_contDiffOn (radialCorrectionCovectorL.contDiff.comp_contDiffOn hQ)).clm_comp
    (contDiffOn_const (c:=sphereSobolevInclusionL 1 0 (by norm_num)))
  exact (hDa.sub contDiffOn_const).sub (contDiffOn_snd.fst.smul hB)

end ShrinkingSpheres
