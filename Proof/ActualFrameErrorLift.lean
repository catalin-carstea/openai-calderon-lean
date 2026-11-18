import Proof.ShiftedDegreeInclusion
import Proof.ActualFrameErrorProducts
import Proof.ActualSecondTraceAssembly
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma flatTwoRaisingL_coarse (j : I) (u : SphereSobolev 2) :
    sphereSobolevInclusionL 1 0 (by norm_num) (flatTwoRaisingL j u)=
      flatOneRaisingL j (sphereSobolevInclusionL 2 1 (by norm_num) u) := by
  have hh := flatRaisingSobolevL_inclusion 2 1 (by norm_num) j
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 1 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact (DFunLike.congr_fun hh u).symm

lemma sphereSobolevShiftedDegreeL_two_coarse (u : SphereSobolev 2) :
    sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevShiftedDegreeL 2 u)=
      sphereSobolevDegreeL (sphereSobolevInclusionL 2 1 (by norm_num) u) := by
  have h := sphereSobolevShiftedDegreeL_inclusion 2 1 (by norm_num) u
  rw [sphereSobolevShiftedDegreeL_one_eq_degree] at h
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 1 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at h
  exact h

/-- Genuine high realization of the leading and bounded first corrections. -/
def firstFrameKnownHighL (d : Data) (y : X) (j : I) : SphereSobolev 2 →L[ℝ] SphereSobolev 1 :=
  (d.radius y)⁻¹ • flatTwoRaisingL j+
    (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)) • sphereSobolevShiftedDegreeL 2+
    (firstFrameAdjointCorrectionSobolevL d y j).comp (sphereSobolevInclusionL 2 1 (by norm_num))

lemma firstFrameKnownHighL_coarse (d : Data) (y : X) (j : I) (u : SphereSobolev 2) :
    sphereSobolevInclusionL 1 0 (by norm_num) (firstFrameKnownHighL d y j u)=
      (actualLeadingFrameAdjointL d j y+firstFrameCorrectionCoarseFamily d j y)
        (sphereSobolevInclusionL 2 1 (by norm_num) u) := by
  simp only [firstFrameKnownHighL,_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_add,map_smul,flatTwoRaisingL_coarse,sphereSobolevShiftedDegreeL_two_coarse,
    firstFrameAdjointCorrectionL_coarse,actualLeadingFrameAdjointL,leadingFrameModelFamily,
    firstFrameCorrectionCoarseFamily]

/-- The actual H1 error output obtained from the SAME physical first adjoint. -/
def firstFrameErrorLift (d : Data) (y : X) (j : I) (u : SphereSobolev 2) (v : SphereSobolev 1) :
    SphereSobolev 1 := v-firstFrameKnownHighL d y j u

lemma firstFrameErrorLift_coarse (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (y : X) (j : I) (u : SphereSobolev 2) (v : SphereSobolev 1)
    (hOut : sphereSobolevInclusionL 1 0 (by norm_num) v=
      completeFirstAdjointFamily d A G j y (sphereSobolevInclusionL 2 1 (by norm_num) u)) :
    sphereSobolevInclusionL 1 0 (by norm_num) (firstFrameErrorLift d y j u v)=
      actualFrameFirstAdjointErrorFamily d A G j y (sphereSobolevInclusionL 2 1 (by norm_num) u) := by
  rw [firstFrameErrorLift,map_sub,hOut,firstFrameKnownHighL_coarse]
  simp only [completeFirstAdjointFamily,_root_.add_apply]
  abel

namespace SecondTraceSectionOutput
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {φ : Field} {L : ℂ →L[ℝ] ℝ} {F : X × X → ℝ} {hF : ContDiff ℝ ∞ F}

def errorLift (P : SecondTraceSectionOutput Y d A G S φ L F hF) (y : X) (j : I) : SphereSobolev 1 :=
  firstFrameErrorLift d y j (ambientSobolevSection 2 (by norm_num) F hF y)
    (ambientSobolevSection 1 (by norm_num) (P.representative j) (P.smooth j) y)

lemma errorLift_coarse (P : SecondTraceSectionOutput Y d A G S φ L F hF) {y : X} (hy : y ∈ Y) (j : I) :
    sphereSobolevInclusionL 1 0 (by norm_num) (P.errorLift y j)=
      actualFrameFirstAdjointErrorFamily d A G j y
        (sphereSobolevInclusionL 2 1 (by norm_num) (ambientSobolevSection 2 (by norm_num) F hF y)) := by
  apply firstFrameErrorLift_coarse d A G y j
  rw [ambientSobolevSection_coarse,ambientSobolevSection_inclusion]
  exact (P.normal j y hy).symm

lemma errorLift_half (P : SecondTraceSectionOutput Y d A G S φ L F hF)
    {CE : ℝ} (E : ActualFrameErrorEndpointPair Y d A G CE) {y : X} (hy : y ∈ Y) (j : I) :
    sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (P.errorLift y j)=
      E.high j y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)
        (ambientSobolevSection 2 (by norm_num) F hF y)) :=
  higher_endpoint_actual_lift _ _ (E.high_coarse j y hy) _ _ (P.errorLift_coarse hy j)

/-- The two-error term in the actual principal section uses the SAME physical
    error lifts and exactly the controlled half-order coefficient product. -/
lemma error_product_actual (P : SecondTraceSectionOutput Y d A G S φ L F hF)
    {CE : ℝ} (E : ActualFrameErrorEndpointPair Y d A G CE) (Q : X → I → I → ℝ)
    {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (∑ i : I,∑ j : I,Q y i j • actualFrameFirstAdjointErrorFamily d A G i y (P.errorLift y j))=
      E.productL Q y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)
        (ambientSobolevSection 2 (by norm_num) F hF y)) :=
  E.product_actual_lifts Q hy _ (P.errorLift y) (fun j => P.errorLift_coarse hy j)
end SecondTraceSectionOutput
end ShrinkingSpheres
