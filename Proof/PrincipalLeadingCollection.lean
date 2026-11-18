import Proof.ScaledLeadingAngularProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Pointwise leading second-trace collection on genuine successive grades.
The inverse-radius derivative and the degree shift cancel before estimating. -/
lemma scaled_leading_second_trace_pair (r c bi bj H : ℝ) (hrc : r*c=1)
    (i j : I) (u : SphereSobolev 2) (vi vj : SphereSobolev 1) (W : SphereSobolev 0) :
    r • (W+
      (c • flatRaisingSobolevL 1 i+bi • sphereSobolevShiftedDegreeL 1) vj+
      (c • flatRaisingSobolevL 1 j+bj • sphereSobolevShiftedDegreeL 1) vi+
      (c • flatRaisingSobolevL 1 i+bi • sphereSobolevShiftedDegreeL 1)
        (c • flatRaisingSobolevL 2 j u+bj • sphereSobolevShiftedDegreeL 2 u)+
      (-c*bi) • sphereSobolevInclusionL 1 0 (by norm_num) (flatRaisingSobolevL 2 j u)+
      H • sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevShiftedDegreeL 2 u))=
      r • (W+bi • sphereSobolevShiftedDegreeL 1 vj+
        bj • sphereSobolevShiftedDegreeL 1 vi+
        H • sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevShiftedDegreeL 2 u)+
        (bi*bj) • sphereSobolevShiftedDegreeL 1 (sphereSobolevShiftedDegreeL 2 u))+
      flatRaisingSobolevL 1 i (vj+bj • sphereSobolevShiftedDegreeL 2 u)+
      flatRaisingSobolevL 1 j (vi+bi • sphereSobolevShiftedDegreeL 2 u)+
      c • flatRaisingSobolevL 1 i (flatRaisingSobolevL 2 j u) := by
  have hCollect {E : Type} [AddCommGroup E] [Module ℝ E]
      (w avj avi dvj dvi p au du ad bd dd aa : E)
      (hP : r • p-bi • au=c • aa+bj • ad+bi • bd+(r*bi*bj) • dd) :
      r • (w+(c • avj+bi • dvj)+(c • avi+bj • dvi)+p+(-c*bi) • au+H • du)=
        r • (w+bi • dvj+bj • dvi+H • du+(bi*bj) • dd)+
          (avj+bj • ad)+(avi+bi • bd)+c • aa := by
    have hp := (sub_eq_iff_eq_add).1 hP
    have hCancel : r*(-c*bi)= -bi := by
      calc
        _ = -(r*c)*bi := by ring
        _ = _ := by rw [hrc];ring
    simp only [smul_add,smul_smul,hCancel,hrc,one_smul]
    rw [hp]
    module
  have h := hCollect W (flatRaisingSobolevL 1 i vj) (flatRaisingSobolevL 1 j vi)
    (sphereSobolevShiftedDegreeL 1 vj) (sphereSobolevShiftedDegreeL 1 vi)
    ((c • flatRaisingSobolevL 1 i+bi • sphereSobolevShiftedDegreeL 1)
      (c • flatRaisingSobolevL 2 j u+bj • sphereSobolevShiftedDegreeL 2 u))
    (sphereSobolevInclusionL 1 0 (by norm_num) (flatRaisingSobolevL 2 j u))
    (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevShiftedDegreeL 2 u))
    (flatRaisingSobolevL 1 i (sphereSobolevShiftedDegreeL 2 u))
    (flatRaisingSobolevL 1 j (sphereSobolevShiftedDegreeL 2 u))
    (sphereSobolevShiftedDegreeL 1 (sphereSobolevShiftedDegreeL 2 u))
    (flatRaisingSobolevL 1 i (flatRaisingSobolevL 2 j u))
    (scaled_leading_angular_product r c bi bj hrc i j u)
  simpa only [_root_.add_apply,_root_.smul_apply,map_add,map_smul] using h

/-- A symmetric principal matrix combines the two mixed leading terms
without any frame differentiation. -/
lemma symmetric_leading_trace_collection (r c : ℝ) (hrc : r*c=1)
    (q : I → I → ℝ) (hq : ∀ i j,q i j=q j i)
    (b : I → ℝ) (H : I → I → ℝ) (u : SphereSobolev 2)
    (v : I → SphereSobolev 1) (W : I → I → SphereSobolev 0) :
    r • (∑ i : I,∑ j : I,q i j • (W i j+
      (c • flatRaisingSobolevL 1 i+b i • sphereSobolevShiftedDegreeL 1) (v j)+
      (c • flatRaisingSobolevL 1 j+b j • sphereSobolevShiftedDegreeL 1) (v i)+
      (c • flatRaisingSobolevL 1 i+b i • sphereSobolevShiftedDegreeL 1)
        (c • flatRaisingSobolevL 2 j u+b j • sphereSobolevShiftedDegreeL 2 u)+
      (-c*b i) • sphereSobolevInclusionL 1 0 (by norm_num) (flatRaisingSobolevL 2 j u)+
      H i j • sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevShiftedDegreeL 2 u)))=
      r • (∑ i : I,∑ j : I,q i j • (W i j+b i • sphereSobolevShiftedDegreeL 1 (v j)+
        b j • sphereSobolevShiftedDegreeL 1 (v i)+
        H i j • sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevShiftedDegreeL 2 u)+
        (b i*b j) • sphereSobolevShiftedDegreeL 1 (sphereSobolevShiftedDegreeL 2 u)))+
      (2:ℝ) • (∑ i : I,∑ j : I,q i j • flatRaisingSobolevL 1 i
        (v j+b j • sphereSobolevShiftedDegreeL 2 u))+
      c • (∑ i : I,∑ j : I,q i j • flatRaisingSobolevL 1 i (flatRaisingSobolevL 2 j u)) := by
  have hSwap : (∑ i : I,∑ j : I,q i j • flatRaisingSobolevL 1 j
      (v i+b i • sphereSobolevShiftedDegreeL 2 u))=
      ∑ i : I,∑ j : I,q i j • flatRaisingSobolevL 1 i
        (v j+b j • sphereSobolevShiftedDegreeL 2 u) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hq j i]
  have hScaled {Z : Type} [AddCommGroup Z] [Module ℝ Z]
      (t : ℝ) (F : I → I → Z) :
      t • (∑ i : I,∑ j : I,q i j • F i j)=
        ∑ i : I,∑ j : I,q i j • (t • F i j) := by
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm t (q i j) (F i j)
  rw [hScaled]
  simp_rw [scaled_leading_second_trace_pair r c (b _) (b _) (H _ _) hrc]
  simp only [smul_add,Finset.sum_add_distrib,← hScaled]
  rw [hSwap]
  module
end ShrinkingSpheres
