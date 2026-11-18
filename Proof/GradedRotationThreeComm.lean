import Proof.GradedRotationDegreeAlgebra
import Proof.SobolevRotationIndexSkew

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

/-- Bilinear commutator expansion between genuinely different grades. -/
lemma graded_three_commutator {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A₀ A₁ A₂ : F →L[ℝ] G) (B₀ B₁ B₂ : E →L[ℝ] F) (p q : I → ℝ) :
    (p 0 • A₀+p 1 • A₁+p 2 • A₂).comp (q 0 • B₀+q 1 • B₁+q 2 • B₂)-
      (q 0 • A₀+q 1 • A₁+q 2 • A₂).comp (p 0 • B₀+p 1 • B₁+p 2 • B₂)=
    (p 0*q 1-p 1*q 0) • (A₀.comp B₁-A₁.comp B₀)+
      (p 0*q 2-p 2*q 0) • (A₀.comp B₂-A₂.comp B₀)+
      (p 1*q 2-p 2*q 1) • (A₁.comp B₂-A₂.comp B₁) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,
    _root_.smul_apply,map_add,map_smul]
  module

def threeRotationL (s : ℝ) (p : I → ℝ) : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  p 0 • sphereSobolevRotationL s 0 1+p 1 • sphereSobolevRotationL s 0 2+
    p 2 • sphereSobolevRotationL s 1 2

def threeRotationBracket (p q : I → ℝ) : I → ℝ :=
  fun k => if k=0 then p 2*q 1-p 1*q 2 else if k=1 then p 0*q 2-p 2*q 0 else p 1*q 0-p 0*q 1

lemma sphereSobolevRotationL_index_self (s : ℝ) (i : I) : sphereSobolevRotationL s i i=0 := by
  have h := sphereSobolevRotationL_index_swap s i i
  apply ContinuousLinearMap.ext
  intro u
  have hu := DFunLike.congr_fun h u
  simp only [_root_.neg_apply] at hu
  have hz : (2:ℝ) • sphereSobolevRotationL s i i u=0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hu
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Exact angular Lie identity with one real derivative lost by the
commutator, and the actual inclusion between its two Sobolev grades. -/
theorem threeRotationL_lie_commutator (s : ℝ) (p q : I → ℝ) :
    (threeRotationL (s-1) p).comp (threeRotationL s q)-
      (threeRotationL (s-1) q).comp (threeRotationL s p)=
    (threeRotationL (s-1) (threeRotationBracket p q)).comp
      (sphereSobolevInclusionL s (s-1) (by linarith)) := by
  rw [threeRotationL,threeRotationL,threeRotationL,threeRotationL,graded_three_commutator]
  simp only [sphereSobolevRotationL_lie_commutator s 0 1 0 2,
    sphereSobolevRotationL_lie_commutator s 0 1 1 2,
    sphereSobolevRotationL_lie_commutator s 0 2 1 2]
  have h10 := sphereSobolevRotationL_index_swap (s-1) 1 0
  simp only [rotationLieRemainderL,show (1:I) ≠ 0 by decide,show (1:I) ≠ 2 by decide,
    show (0:I) ≠ 2 by decide,show (0:I) ≠ 1 by decide,show (2:I) ≠ 1 by decide,
    ite_false,ite_true,sub_zero,zero_sub,add_zero,sphereSobolevRotationL_index_self,h10]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,
    _root_.neg_apply,_root_.smul_apply,threeRotationL,threeRotationBracket,
    show (1:I) ≠ 0 by decide,show (2:I) ≠ 0 by decide,show (2:I) ≠ 1 by decide,
    ite_false,ite_true,ContinuousLinearMap.zero_apply,sub_zero,zero_sub]
  module

end ShrinkingSpheres
