import Proof.NormalFrameRadialAdjointTaylorModel

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
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL

lemma normalFrameRadialAdjointTaylorFamily_parallel (d : Data)
    (Da : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (y a : X) (t : ℝ) :
    normalFrameRadialAdjointTaylorFamily d Da (normalFrameParallelCurve d.γ d.frame d.radius y a t) =
      Da (normalFrameParallelCurve d.γ d.frame d.radius y a t)-sphereSobolevDegreeL-d.radius y •
        (coarseFirstRadialVariationL 1 (parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) t)).adjoint.comp
          (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have hB : radialCorrectionCovectorL (normalFrameFirstCovector d.γ d.g₁
      (normalFrameParallelCurve d.γ d.frame d.radius y a t)) =
      coarseFirstRadialVariationL 1 (parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) t) := by
    rw [normalFrameFirstCovector_parallel,radialCorrectionCovectorL_apply]
  exact congrArg (fun B : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    Da (normalFrameParallelCurve d.γ d.frame d.radius y a t)-sphereSobolevDegreeL-d.radius y •
      B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) hB

lemma Background.normalFrameRadialAdjointTaylorFamily_radius {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (Da : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (t : ℝ) :
    normalFrameRadialAdjointTaylorFamily d Da (normalFrameRadiusCurve d.frame d.radius y t) =
      Da (normalFrameRadiusCurve d.frame d.radius y t)-sphereSobolevDegreeL-d.radius y •
        (coarseFirstRadialVariationL 1 ((1+t) • firstDensityLogCovector d y)).adjoint.comp
          (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have hCov : normalFrameFirstCovector d.γ d.g₁ (normalFrameRadiusCurve d.frame d.radius y t) = firstDensityLogCovector d y :=
    h.normalFrameFirstCovector_actual hΩ hK hy
  let J : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
  have hAdj : (radialCorrectionCovectorL ((1+t) • firstDensityLogCovector d y)).adjoint =
      (1+t) • (radialCorrectionCovectorL (firstDensityLogCovector d y)).adjoint := by
    change J (radialCorrectionCovectorL ((1+t) • firstDensityLogCovector d y)) =
      (1+t) • J (radialCorrectionCovectorL (firstDensityLogCovector d y))
    rw [radialCorrectionCovectorL.map_smul,J.map_smul]
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hBB := radialCorrectionCovectorL_apply ((1+t) • firstDensityLogCovector d y)
  have hBA := (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T.adjoint) hBB.symm).trans hAdj
  have hComp : (coarseFirstRadialVariationL 1 ((1+t) • firstDensityLogCovector d y)).adjoint.comp I0 =
      (1+t) • (radialCorrectionCovectorL (firstDensityLogCovector d y)).adjoint.comp I0 :=
    (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T.comp I0) hBA).trans
      (ContinuousLinearMap.smul_comp _ _ _)
  have hTerm : ((1+t)*d.radius y) •
      (radialCorrectionCovectorL (firstDensityLogCovector d y)).adjoint.comp I0 =
      d.radius y • (coarseFirstRadialVariationL 1 ((1+t) • firstDensityLogCovector d y)).adjoint.comp I0 := by
    calc
      _ = d.radius y • ((1+t) • (radialCorrectionCovectorL (firstDensityLogCovector d y)).adjoint.comp I0) := by
        exact (congrArg (fun s : ℝ => s • (radialCorrectionCovectorL (firstDensityLogCovector d y)).adjoint.comp I0)
          (mul_comm (1+t) (d.radius y))).trans
          (mul_smul (d.radius y) (1+t) _)
      _ = _ := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => d.radius y • T) hComp.symm
  have hCovTerm := congrArg (fun q : X →L[ℝ] ℝ => ((1+t)*d.radius y) •
    (radialCorrectionCovectorL q).adjoint.comp I0) hCov
  exact congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    Da (normalFrameRadiusCurve d.frame d.radius y t)-sphereSobolevDegreeL-T) (hCovTerm.trans hTerm)

end ShrinkingSpheres
