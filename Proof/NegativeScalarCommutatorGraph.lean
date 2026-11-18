import Proof.RelativeCoframeSobolevMultiplier
import Proof.FirstAdjointCorrectionDegreeCommutator
import Proof.RadialCorrectionHalfLinear
import Proof.ClosedHalfScalarCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A bounded coarse operator and its genuine negative-half realization give
    a genuine order-zero commutator without any angular order loss. -/
lemma bounded_coarse_negative_commutator
    (B0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (BN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (M1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (M0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (MN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hB : ∀ u,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (B0 u) =
      BN (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u))
    (hM : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (M1 u) =
      M0 (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (hMN : ∀ u,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (M0 u) =
      MN (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u)) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      ((B0.comp (sphereSobolevInclusionL 1 0 (by norm_num))).comp M1-
        M0.comp (B0.comp (sphereSobolevInclusionL 1 0 (by norm_num)))) =
      (BN.comp MN-MN.comp BN).comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,map_sub,hM,hB,hMN,
    sphereSobolevInclusionL_trans_apply]

def coordinateDegreeCommutatorNegativeL (j : I) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  radialCorrectionSobolevL (-(1/2:ℝ)) (EuclideanSpace.proj (𝕜:=ℝ) j)-
    radialCorrectionNegativeAdjointMapL (EuclideanSpace.proj (𝕜:=ℝ) j)

lemma coordinateDegreeCommutator_negative_coarse (j : I) (u : SphereSobolev 0) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (coordinateDegreeCommutatorL j u) =
      coordinateDegreeCommutatorNegativeL j (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u) := by
  simp only [coordinateDegreeCommutatorL,coordinateDegreeCommutatorNegativeL,_root_.sub_apply,map_sub,
    radialCorrectionNegativeAdjoint_coarse]
  congr 1
  rw [← radialCorrectionSobolevL_zero]
  exact sphereSobolevInclusionL_radialDrift sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    0 (-(1/2:ℝ)) (by norm_num) (radialCorrectionVector _) u

def relativeCoframeDegreeCommutatorNegativeL (g : MetricField) (v : X) (p : NormalFrameRelativeParameter) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ j : I,normalFrameRelativeCoframeValue g v j p • coordinateDegreeCommutatorNegativeL j

lemma degree_normal_coframe_negative_commutator (g : MetricField) (v : X) (p : NormalFrameRelativeParameter) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (sphereSobolevDegreeL.comp (relativeCoframeNormalSobolevL 1 g v p)-
        (relativeCoframeNormalSobolevL 0 g v p).comp sphereSobolevDegreeL) =
      (relativeCoframeDegreeCommutatorNegativeL g v p).comp
        (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevDegreeL (relativeCoframeNormalSobolevL 1 g v p u)-
        relativeCoframeNormalSobolevL 0 g v p (sphereSobolevDegreeL u)) = _
  simp only [relativeCoframeNormalSobolevL,relativeCoframeDegreeCommutatorNegativeL,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,map_sum,map_smul]
  rw [← Finset.sum_sub_distrib,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← smul_sub,map_smul]
  congr 1
  have hh := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
    (degree_coordinateMultiplier_commutator j)
  change sphereSobolevDegreeL (coordinateMultiplierSobolevL 1 j u)-
      coordinateMultiplierSobolevL 0 j (sphereSobolevDegreeL u) =
        coordinateDegreeCommutatorL j (sphereSobolevInclusionL 1 0 (by norm_num) u) at hh
  rw [hh,coordinateDegreeCommutator_negative_coarse,sphereSobolevInclusionL_trans_apply]
end ShrinkingSpheres
