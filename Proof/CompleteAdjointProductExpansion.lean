import Proof.RadiusOperatorProductExpansion
import Proof.ActualFrameErrorLift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Complete actual zero-base adjoint product, collected into the leading
    model, F/raising, F/degree, F/F, E/raising, E/degree, F/E and E/E groups.
    All error outputs are the SAME high lift in the physical second trace. -/
lemma complete_first_adjoint_product_expansion (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (y : X) (hr : d.radius y ≠ 0) (i j : I) (u : SphereSobolev 2) (v : SphereSobolev 1) :
    let b := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
    let W := firstFrameAdjointCorrectionSobolevL d y j (sphereSobolevInclusionL 2 1 (by norm_num) u)
    let e := firstFrameErrorLift d y j u v
    let Ei := actualFrameFirstAdjointErrorFamily d A G i y
    d.radius y • completeFirstAdjointFamily d A G i y v=
      d.radius y • actualLeadingFrameAdjointL d i y
        ((d.radius y)⁻¹ • flatTwoRaisingL j u+b j • sphereSobolevShiftedDegreeL 2 u)+
      (flatOneRaisingL i W+firstFrameAdjointCorrectionL d y i
        (flatOneRaisingL j (sphereSobolevInclusionL 2 1 (by norm_num) u)))+
      ((d.radius y*b i) • sphereSobolevDegreeL W+
        (d.radius y*b j) • firstFrameAdjointCorrectionL d y i
          (sphereSobolevDegreeL (sphereSobolevInclusionL 2 1 (by norm_num) u)))+
      d.radius y • firstFrameAdjointCorrectionL d y i (sphereSobolevInclusionL 1 0 (by norm_num) W)+
      (flatOneRaisingL i e+Ei (flatTwoRaisingL j u))+
      ((d.radius y*b i) • sphereSobolevDegreeL e+(d.radius y*b j) • Ei (sphereSobolevShiftedDegreeL 2 u))+
      d.radius y • (firstFrameAdjointCorrectionL d y i (sphereSobolevInclusionL 1 0 (by norm_num) e)+Ei W)+
      d.radius y • Ei e := by
  dsimp only
  let b := fun k => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y k)
  let e := firstFrameErrorLift d y j u v
  have hV : (d.radius y)⁻¹ • flatTwoRaisingL j u+b j • sphereSobolevShiftedDegreeL 2 u+
      firstFrameAdjointCorrectionSobolevL d y j (sphereSobolevInclusionL 2 1 (by norm_num) u)+e=v := by
    change firstFrameKnownHighL d y j u+(v-firstFrameKnownHighL d y j u)=v
    abel
  have hC : (d.radius y)⁻¹ • flatOneRaisingL i+b i • sphereSobolevDegreeL+
      (firstFrameAdjointCorrectionL d y i).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
        actualFrameFirstAdjointErrorFamily d A G i y=completeFirstAdjointFamily d A G i y := rfl
  have h := radius_operator_product_expansion (d.radius y) (d.radius y)⁻¹ (b i) (b j)
    (mul_inv_cancel₀ hr) (flatOneRaisingL i) (flatOneRaisingL j) sphereSobolevDegreeL
    (flatTwoRaisingL j) (sphereSobolevShiftedDegreeL 2) (firstFrameAdjointCorrectionL d y i)
    (firstFrameAdjointCorrectionSobolevL d y j) (actualFrameFirstAdjointErrorFamily d A G i y)
    (sphereSobolevInclusionL 1 0 (by norm_num)) (sphereSobolevInclusionL 2 1 (by norm_num)) u e
    (flatTwoRaisingL_coarse j u) (sphereSobolevShiftedDegreeL_two_coarse u)
  have hLeft := congrArg₂
    (fun (B : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (w : SphereSobolev 1) => d.radius y • B w)
    hC.symm hV.symm
  exact hLeft.trans (h.trans (by rfl))
end ShrinkingSpheres
