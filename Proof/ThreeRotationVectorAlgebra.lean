import Proof.GradedRotationThreeComm
import Proof.FrameConnectionCurvature

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation

def threeRotationVectorL (p : I → ℝ) : X →L[ℝ] X :=
  p 0 • rotationVectorL 0 1+p 1 • rotationVectorL 0 2+p 2 • rotationVectorL 1 2

def threeRotationVectorMapL : (I → ℝ) →L[ℝ] X →L[ℝ] X :=
  (ContinuousLinearMap.proj 0).smulRight (rotationVectorL 0 1)+
    (ContinuousLinearMap.proj 1).smulRight (rotationVectorL 0 2)+
    (ContinuousLinearMap.proj 2).smulRight (rotationVectorL 1 2)

lemma threeRotationVectorMapL_apply (p : I → ℝ) : threeRotationVectorMapL p=threeRotationVectorL p := by
  simp only [threeRotationVectorMapL,threeRotationVectorL,_root_.add_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

lemma threeRotationVectorL_skew (p : I → ℝ) (i j : I) :
    threeRotationVectorL p (axis i) j= -threeRotationVectorL p (axis j) i := by
  fin_cases i <;> fin_cases j <;>
    simp [threeRotationVectorL,_root_.add_apply,_root_.smul_apply,
      rotationVectorL_apply,rotationVector,axis,PiLp.single_apply] <;> ring

/-- The vector-field representation and the action on functions have
opposite Lie signs. This is an identity on the finite base tangent space. -/
theorem threeRotationVectorL_commutator (p q : I → ℝ) :
    (threeRotationVectorL p).comp (threeRotationVectorL q)-
      (threeRotationVectorL q).comp (threeRotationVectorL p)=
        -threeRotationVectorL (threeRotationBracket p q) := by
  apply ContinuousLinearMap.ext
  intro z
  ext k
  fin_cases k <;>
    simp [threeRotationVectorL,threeRotationBracket,ContinuousLinearMap.comp_apply,
      _root_.add_apply,_root_.sub_apply,_root_.smul_apply,_root_.neg_apply,
      rotationVectorL_apply,rotationVector,axis,PiLp.single_apply] <;> ring

def threeSkewCoordinates (A : I → I → ℝ) : I → ℝ :=
  fun k => if k=0 then A 0 1 else if k=1 then A 0 2 else A 1 2

lemma skew_sum_rotationVectorL_eq_three (A : I → I → ℝ) (hA : ∀ i j,A i j= -A j i) :
    (∑ i : I,∑ j : I,((1/2:ℝ)*A i j) • rotationVectorL i j)=
      threeRotationVectorL (threeSkewCoordinates A) := by
  have hD (i : I) : A i i=0 := by linarith only [hA i i]
  apply ContinuousLinearMap.ext
  intro z
  ext k
  fin_cases k <;>
    simp [threeRotationVectorL,threeSkewCoordinates,Fin.sum_univ_three,
      _root_.sum_apply,_root_.smul_apply,_root_.add_apply,rotationVectorL_apply,
      rotationVector,axis,PiLp.single_apply,hD,hA 1 0,hA 2 0,hA 2 1] <;> ring

lemma frameConnectionOperator_eq_three (g : MetricField) (e : Frame) (y a : X)
    (hA : ∀ i j,frameConnectionCoefficient g e y a i j= -frameConnectionCoefficient g e y a j i) :
    frameConnectionOperator g e y a=
      threeRotationVectorL (threeSkewCoordinates (frameConnectionCoefficient g e y a)) := by
  rw [frameConnectionOperator_apply]
  exact skew_sum_rotationVectorL_eq_three _ hA

end ShrinkingSpheres
