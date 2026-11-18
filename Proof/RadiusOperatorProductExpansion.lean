import Proof.BoundedCompositionCross
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace ShrinkingSpheres
variable {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Exact collection of leading, bounded-correction and error products. The
    inclusions refer to the same actual high outputs, and r*c=1 cancels the
    inverse radius only in the two raising cross terms. -/
lemma radius_operator_product_expansion (r c bi bj : ℝ) (hrc : r*c=1)
    (A B D : V →L[ℝ] W) (AH DH : U →L[ℝ] V)
    (F : W →L[ℝ] W) (FH : V →L[ℝ] V) (E : V →L[ℝ] W)
    (I : V →L[ℝ] W) (J : U →L[ℝ] V) (u : U) (v : V)
    (hA : I (AH u)=B (J u)) (hD : I (DH u)=D (J u)) :
    r • ((c • A+bi • D+F.comp I+E) (c • AH u+bj • DH u+FH (J u)+v))=
      r • ((c • A+bi • D) (c • AH u+bj • DH u))+
      (A (FH (J u))+F (B (J u)))+
      ((r*bi) • D (FH (J u))+(r*bj) • F (D (J u)))+
      r • F (I (FH (J u)))+
      (A v+E (AH u))+
      ((r*bi) • D v+(r*bj) • E (DH u))+
      r • (F (I v)+E (FH (J u)))+
      r • E v := by
  have hrca (a : ℝ) : r*c*a=a := by rw [hrc,one_mul]
  have hrac (a : ℝ) : r*a*c=a := by
    calc
      _ = r*c*a := by ring
      _ = a := hrca a
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_add,map_smul,hA,hD,smul_add,smul_smul,← mul_assoc,hrc,hrac,one_smul]
  module
end ShrinkingSpheres
