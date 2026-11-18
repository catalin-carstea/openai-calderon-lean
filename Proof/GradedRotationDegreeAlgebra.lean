import Proof.HarmonicRotationLieAlgebra
import Proof.Archive.SphereSobolevSingleRotationAngleDerivative
import Proof.Archive.SphereSobolevShiftedPhysicalDegree
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.RotationLieAlgebra

def rotationLieRemainderL (s : ℝ) (i j a b : I) :
    SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  (if j=a then sphereSobolevRotationL s i b else 0)-
  (if j=b then sphereSobolevRotationL s i a else 0)-
  (if i=a then sphereSobolevRotationL s j b else 0)+
  (if i=b then sphereSobolevRotationL s j a else 0)

lemma sphereSobolevRotationL_lie_commutator (s : ℝ) (i j a b : I) :
    (sphereSobolevRotationL (s-1) i j).comp (sphereSobolevRotationL s a b)-
      (sphereSobolevRotationL (s-1) a b).comp (sphereSobolevRotationL s i j)=
    (rotationLieRemainderL (s-1) i j a b).comp
      (sphereSobolevInclusionL s (s-1) (by linarith)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext ((s-1)-1)
  intro n
  have hIf (P : Prop) [Decidable P] (x : SphereSobolev (s-1) →L[ℝ] SphereSobolev ((s-1)-1)) :
      sphereSobolevCoefficientL ((s-1)-1) n
        ((if P then x else 0) (sphereSobolevInclusionL s (s-1) (by linarith) u))=
      if P then sphereSobolevCoefficientL ((s-1)-1) n
        (x (sphereSobolevInclusionL s (s-1) (by linarith) u)) else 0 := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,ContinuousLinearMap.zero_apply,map_zero]
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,_root_.add_apply,
    rotationLieRemainderL,map_sub,map_add,hIf,
    sphereSobolevCoefficientL_rotation,sphereSobolevCoefficientL_inclusion]
  exact harmonicSphereRotation_lie_commutator n i j a b (sphereSobolevCoefficientL s n u)

lemma norm_rotationLieRemainderL_le (s : ℝ) (i j a b : I) :
    ‖rotationLieRemainderL s i j a b‖ ≤ 4*Real.sqrt 2 := by
  have hIf (P : Prop) [Decidable P] (k l : I) :
      ‖(if P then sphereSobolevRotationL s k l else 0)‖ ≤ Real.sqrt 2 := by
    by_cases hP : P
    · simpa only [hP,ite_true] using norm_sphereSobolevRotationL_le s k l
    · simp only [hP,ite_false,norm_zero];exact Real.sqrt_nonneg 2
  unfold rotationLieRemainderL
  calc
    _ ≤ ‖(if j=a then sphereSobolevRotationL s i b else 0)-
        (if j=b then sphereSobolevRotationL s i a else 0)-
        (if i=a then sphereSobolevRotationL s j b else 0)‖+
        ‖(if i=b then sphereSobolevRotationL s j a else 0)‖ := norm_add_le _ _
    _ ≤ _ := by
      have h1 := norm_sub_le (if j=a then sphereSobolevRotationL s i b else 0)
        (if j=b then sphereSobolevRotationL s i a else 0)
      have h2 := norm_sub_le ((if j=a then sphereSobolevRotationL s i b else 0)-
        (if j=b then sphereSobolevRotationL s i a else 0))
        (if i=a then sphereSobolevRotationL s j b else 0)
      linarith [hIf (j=a) i b,hIf (j=b) i a,hIf (i=a) j b,hIf (i=b) j a]

lemma sphereSobolevShiftedDegreeL_rotation_commute (s : ℝ) (i j : I) :
    (sphereSobolevShiftedDegreeL (s-1)).comp (sphereSobolevRotationL s i j)=
      (sphereSobolevRotationL (s-1) i j).comp (sphereSobolevShiftedDegreeL s) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext ((s-1)-1)
  intro n
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_shiftedDegree,
    sphereSobolevCoefficientL_rotation,map_smul]
end ShrinkingSpheres
