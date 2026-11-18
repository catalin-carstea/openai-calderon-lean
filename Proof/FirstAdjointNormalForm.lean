import Proof.BoundaryCoefficientNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def modelBoundaryAdjointL (P : I → SmoothCoefficientJets 2) (r b : ℝ) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  r⁻¹ • (adjointBoundaryTangentialL P+sphereSobolevDegreeL.comp
    (oneBoundaryCoefficientMulL (vectorNormalJet P)))+b • sphereSobolevDegreeL

def firstBoundaryAdjointCorrectionL (P : I → SmoothCoefficientJets 2)
    (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0) (r b : ℝ) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  B.adjoint.comp (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet P))))+
    (r*b) • B.adjoint

def radialAdjointTaylorRemainderL (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0) (r : ℝ) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  Da-sphereSobolevDegreeL-r • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))

def firstBoundaryAdjointRemainderL (P C : I → SmoothCoefficientJets 2)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (r b : ℝ) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (r⁻¹ • (radialAdjointTaylorRemainderL Da B r).comp (oneBoundaryCoefficientMulL (vectorNormalJet P))+
    b • radialAdjointTaylorRemainderL Da B r)+r⁻¹ • boundaryGradientAdjointL C Da

/-- Exact first-adjoint decomposition. The first radial correction acts on L2;
    its normal multiplier is transported by the actual H1/L2 compatibility. -/
theorem movingBoundaryHorizontalAdjointL_normal_form (P C : I → SmoothCoefficientJets 2)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (r b : ℝ) (hr : r ≠ 0) :
    movingBoundaryHorizontalAdjointL P C Da r b = modelBoundaryAdjointL P r b+
      (firstBoundaryAdjointCorrectionL P B r b).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
      firstBoundaryAdjointRemainderL P C Da B r b := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let Mn := oneBoundaryCoefficientMulL (vectorNormalJet P)
  let Cn := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet P)))
  let R := radialAdjointTaylorRemainderL Da B r
  have hBreak (v : SphereSobolev 1) : Da v = sphereSobolevDegreeL v+r • B.adjoint (I0 v)+R v := by
    change Da v = sphereSobolevDegreeL v+r • B.adjoint (I0 v)+
      (Da v-sphereSobolevDegreeL v-r • B.adjoint (I0 v))
    abel
  apply ContinuousLinearMap.ext
  intro v
  have hCompat : I0 (Mn v) = Cn (I0 v) := oneBoundaryCoefficientMulL_coarse (vectorNormalJet P) v
  have hBreakM : Da (Mn v) = sphereSobolevDegreeL (Mn v)+r • B.adjoint (Cn (I0 v))+R (Mn v) :=
    (hBreak (Mn v)).trans (congrArg (fun w : SphereSobolev 0 =>
      sphereSobolevDegreeL (Mn v)+r • B.adjoint w+R (Mn v)) hCompat)
  let t := adjointBoundaryTangentialL P v
  let e := boundaryGradientAdjointL C Da v
  have hExpand := congrArg₂ (fun x y : SphereSobolev 0 => (r⁻¹ • (t+x)+b • y)+r⁻¹ • e) hBreakM (hBreak v)
  change (r⁻¹ • (t+Da (Mn v))+b • Da v)+r⁻¹ • e =
    ((r⁻¹ • (t+sphereSobolevDegreeL (Mn v))+b • sphereSobolevDegreeL v)+
      (B.adjoint (Cn (I0 v))+(r*b) • B.adjoint (I0 v)))+
      ((r⁻¹ • R (Mn v)+b • R v)+r⁻¹ • e)
  exact hExpand.trans (by
    simp only [smul_add,smul_smul,inv_mul_cancel₀ hr,one_smul]
    module)

theorem norm_firstBoundaryAdjointCorrectionL_le (P : I → SmoothCoefficientJets 2)
    (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0) (r b CB C0 Cbeta : ℝ)
    (hr : 0 ≤ r) (hCB : 0 ≤ CB) (hC0 : 0 ≤ C0) (hCbeta : 0 ≤ Cbeta)
    (hB : ‖B‖ ≤ CB)
    (hNormal : ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet P)))‖ ≤ C0)
    (hBeta : r*|b| ≤ Cbeta) :
    ‖firstBoundaryAdjointCorrectionL P B r b‖ ≤ CB*(C0+Cbeta) := by
  have hBadj : ‖B.adjoint‖ ≤ CB := (ContinuousLinearMap.adjoint.norm_map B).le.trans hB
  have hFirst : ‖B.adjoint.comp (coarseSphereScalarMulL
      (smoothSphereValue (coefficientSmoothData (vectorNormalJet P))))‖ ≤ CB*C0 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hBadj hNormal (norm_nonneg _) hCB)
  have hSecond : ‖(r*b) • B.adjoint‖ ≤ Cbeta*CB := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hr]
    exact mul_le_mul hBeta hBadj (norm_nonneg _) hCbeta
  exact (norm_add_le _ _).trans ((add_le_add hFirst hSecond).trans_eq (by ring))

theorem norm_firstBoundaryAdjointRemainderL_le (P C : I → SmoothCoefficientJets 2)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (r b C1 Cbeta CJ CE : ℝ) (hr : 0 < r)
    (hC1 : 0 ≤ C1) (hCbeta : 0 ≤ Cbeta) (hCJ : 0 ≤ CJ) (hCE : 0 ≤ CE)
    (hNormal : ‖oneBoundaryCoefficientMulL (vectorNormalJet P)‖ ≤ C1)
    (hBeta : r*|b| ≤ Cbeta)
    (hR : ‖radialAdjointTaylorRemainderL Da B r‖ ≤ CJ*r^2)
    (hCenter : ‖r⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*r) :
    ‖firstBoundaryAdjointRemainderL P C Da B r b‖ ≤ (CJ*C1+Cbeta*CJ+CE)*r := by
  let R := radialAdjointTaylorRemainderL Da B r
  have hFirst : ‖r⁻¹ • R.comp (oneBoundaryCoefficientMulL (vectorNormalJet P))‖ ≤ CJ*C1*r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ r⁻¹*((CJ*r^2)*C1) := mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hR hNormal (norm_nonneg _) (by positivity)))
        (inv_nonneg.mpr hr.le)
      _ = _ := by field_simp <;> ring
  have hSecond : ‖b • R‖ ≤ Cbeta*CJ*r := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |b| *(CJ*r^2) := mul_le_mul_of_nonneg_left hR (abs_nonneg b)
      _ = (r*|b|)*CJ*r := by ring
      _ ≤ _ := by gcongr
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hFirst hSecond) hCenter).trans_eq (by ring))

end ShrinkingSpheres
