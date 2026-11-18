import Proof.FlatRaisingHigherAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma two_level_raising_degree_commutator (j : I) (u : SphereSobolev 2) :
    sphereSobolevShiftedDegreeL 1 (flatRaisingSobolevL 2 j u)-
      flatRaisingSobolevL 1 j (sphereSobolevShiftedDegreeL 2 u)=
        sphereSobolevInclusionL 1 0 (by norm_num) (flatRaisingSobolevL 2 j u) := by
  have h := DFunLike.congr_fun (degree_flatRaisingSobolev_commutator 2 j) u
  have hD : sphereSobolevShiftedDegreeL ((2:ℝ)-1)=sphereSobolevShiftedDegreeL 1 := by
    rw [show (2:ℝ)-1=1 by norm_num]
  have hA : flatRaisingSobolevL ((2:ℝ)-1) j=flatRaisingSobolevL 1 j := by
    rw [show (2:ℝ)-1=1 by norm_num]
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) (((2:ℝ)-1)-1) (by norm_num)=
      sphereSobolevInclusionL 1 0 (by norm_num) := by congr 1 <;> norm_num
  simpa only [_root_.sub_apply,ContinuousLinearMap.comp_apply,hD,hA,hI] using h

/-- The degree shift cancels exactly the inverse-radius derivative in the
    leading physical adjoint product, on genuine successive Sobolev grades. -/
lemma scaled_leading_angular_product (r c bi bj : ℝ) (hrc : r*c=1)
    (i j : I) (u : SphereSobolev 2) :
    r • ((c • flatRaisingSobolevL 1 i+bi • sphereSobolevShiftedDegreeL 1)
      (c • flatRaisingSobolevL 2 j u+bj • sphereSobolevShiftedDegreeL 2 u))-
        bi • sphereSobolevInclusionL 1 0 (by norm_num) (flatRaisingSobolevL 2 j u)=
      c • flatRaisingSobolevL 1 i (flatRaisingSobolevL 2 j u)+
      bj • flatRaisingSobolevL 1 i (sphereSobolevShiftedDegreeL 2 u)+
      bi • flatRaisingSobolevL 1 j (sphereSobolevShiftedDegreeL 2 u)+
      (r*bi*bj) • sphereSobolevShiftedDegreeL 1 (sphereSobolevShiftedDegreeL 2 u) := by
  have hComm := (sub_eq_iff_eq_add).1 (two_level_raising_degree_commutator j u)
  have hrac (a : ℝ) : r*a*c=a := by rw [mul_right_comm r a c,hrc,one_mul]
  simp only [_root_.add_apply,_root_.smul_apply,map_add,map_smul,hComm,
    smul_add,smul_smul,← mul_assoc,hrc,hrac]
  module
end ShrinkingSpheres
