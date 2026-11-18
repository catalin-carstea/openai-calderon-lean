import Proof.NativeTaylorGeneratorSystem
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Physical Sobolev inclusion commutes with the rotation Lie remainder. -/
lemma rotationLieRemainderL_inclusion (s t : ℝ) (hst : t ≤ s) (i j a b : I) :
    (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (rotationLieRemainderL s i j a b)=
      (rotationLieRemainderL t i j a b).comp (sphereSobolevInclusionL s t hst) := by
  have hIf (P : Prop) [Decidable P] (k l : I) :
      (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp
        (if P then sphereSobolevRotationL s k l else 0)=
      (if P then sphereSobolevRotationL t k l else 0).comp (sphereSobolevInclusionL s t hst) := by
    by_cases hp : P
    · simpa only [hp,ite_true] using (sphereSobolevRotationL_inclusion s t hst k l).symm
    · simp only [hp,ite_false,ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]
  simp only [rotationLieRemainderL,ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.add_comp,ContinuousLinearMap.sub_comp,hIf]

def taylorGeneratorHigherCommutator
    (D : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (R : I → I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
    TaylorGeneratorIndex → TaylorGeneratorIndex →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  | .taylor,.degree => D
  | .degree,.taylor => -D
  | .taylor,.rotation i j => -R i j
  | .rotation i j,.taylor => R i j
  | .rotation i j,.rotation a b => rotationLieRemainderL (3/2:ℝ) i j a b
  | _,_ => 0

lemma taylorGeneratorHigherCommutator_compatible
    (D : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (R : I → I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Dl : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Rl : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hD : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp D=
      Dl.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hR : ∀ i j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (R i j)=
      (Rl i j).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (a b : TaylorGeneratorIndex) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (taylorGeneratorHigherCommutator D R a b)=
      (taylorGeneratorCommutator Dl Rl a b).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hRR (i j k l : I) :
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (rotationLieRemainderL (3/2:ℝ) i j k l)=
      (rotationLieRemainderL (1/2:ℝ) i j k l).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    have hh := rotationLieRemainderL_inclusion (3/2:ℝ) (1/2:ℝ) (by norm_num) i j k l
    have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1/2:ℝ)-1) (by norm_num)=
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
    rw [hI] at hh
    exact hh
  cases a <;> cases b <;>
    simp only [taylorGeneratorHigherCommutator,taylorGeneratorCommutator,
      ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_neg,ContinuousLinearMap.neg_comp,hD,hR,hRR]

/-- The same radius weights bound all higher generator-commutator jets. -/
lemma taylorGeneratorHigherCommutator_jets
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (D : P → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (R : I → I → P → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (p : P) (J : ℕ) (r B : ℝ) (hB : 0 ≤ B) (hRot : 4*Real.sqrt 2 ≤ B)
    (hD : SmoothFiniteJetBound D p J (B*r^2))
    (hR : ∀ i j,SmoothFiniteJetBound (R i j) p J (B*r^2))
    (a b : TaylorGeneratorIndex) :
    SmoothFiniteJetBound (fun x => taylorGeneratorHigherCommutator (D x) (fun i j => R i j x) a b)
      p J (B*(taylorGeneratorWeight r a*taylorGeneratorWeight r b)) := by
  have hZero (C : ℝ) (hC : 0 ≤ C) :
      SmoothFiniteJetBound (fun _ : P => (0 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))) p J C := by
    exact (SmoothFiniteJetBound.constant (0 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) p J).weaken (by simpa only [norm_zero] using hC)
  have hNegD : SmoothFiniteJetBound (fun x => -D x) p J (B*r^2) := by
    simpa only [neg_one_smul,abs_neg,abs_one,one_mul] using hD.const_smul (-1)
  have hNegR (i j : I) : SmoothFiniteJetBound (fun x => -R i j x) p J (B*r^2) := by
    simpa only [neg_one_smul,abs_neg,abs_one,one_mul] using (hR i j).const_smul (-1)
  cases a <;> cases b
  · exact hZero _ (mul_nonneg hB (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  · simpa only [taylorGeneratorHigherCommutator,taylorGeneratorWeight,mul_one] using hD
  · simpa only [taylorGeneratorHigherCommutator,taylorGeneratorWeight,mul_one] using hNegR _ _
  · simpa only [taylorGeneratorHigherCommutator,taylorGeneratorWeight,one_mul] using hNegD
  · exact hZero _ (by simpa only [taylorGeneratorWeight,one_mul,mul_one] using hB)
  · exact hZero _ (by simpa only [taylorGeneratorWeight,one_mul,mul_one] using hB)
  · simpa only [taylorGeneratorHigherCommutator,taylorGeneratorWeight,one_mul] using hR _ _
  · exact hZero _ (by simpa only [taylorGeneratorWeight,one_mul,mul_one] using hB)
  · rename_i i j k l
    exact (SmoothFiniteJetBound.constant (rotationLieRemainderL (3/2:ℝ) i j k l) p J).weaken
      (by simpa only [taylorGeneratorWeight,one_mul,mul_one] using
        (norm_rotationLieRemainderL_le (3/2:ℝ) i j k l).trans hRot)
end ShrinkingSpheres
