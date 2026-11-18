import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Operator.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ShrinkingSpheres

/-- A common inverse bound for operators in a fixed norm neighborhood of an
    invertible reference operator. Invertibility of the perturbed operator can
    come independently from coercive elliptic theory. -/
theorem inverse_norm_le_twice_of_half_perturbation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A A0 : E →L[ℝ] F) (hA : A.IsInvertible) (hA0 : A0.IsInvertible)
    (B : ℝ) (hB : 0 ≤ B) (hInv : ‖A0.inverse‖ ≤ B)
    (hSmall : B*‖A-A0‖ ≤ (1/2:ℝ)) : ‖A.inverse‖ ≤ 2*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  let x := A.inverse y
  have h0 : ‖x‖ ≤ B*‖A0 x‖ := by
    calc
      ‖x‖ = ‖A0.inverse (A0 x)‖ := congrArg norm (hA0.inverse_apply_self x).symm
      _ ≤ ‖A0.inverse‖*‖A0 x‖ := A0.inverse.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right hInv (norm_nonneg _)
  have hd : ‖(A-A0) x‖ ≤ ‖A-A0‖*‖x‖ := (A-A0).le_opNorm x
  have ht : ‖A0 x‖ ≤ ‖A x‖+‖(A-A0) x‖ := by
    calc
      ‖A0 x‖ = ‖A x-(A-A0) x‖ := by simp only [ContinuousLinearMap.sub_apply]; congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hh : B*‖A0 x‖ ≤ B*‖y‖+B*‖A-A0‖*‖x‖ := by
    have h := ht.trans (add_le_add le_rfl hd)
    rw [hA.self_apply_inverse y] at h
    have hh := mul_le_mul_of_nonneg_left h hB
    nlinarith only [hh]
  have hs := mul_le_mul_of_nonneg_right hSmall (norm_nonneg x)
  change ‖x‖ ≤ (2*B)*‖y‖
  nlinarith only [h0,hh,hs]

/-- Exact resolvent identity for the canonical Banach inverses. -/
theorem inverse_sub_inverse_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A A0 : E →L[ℝ] F) (hA : A.IsInvertible) (hA0 : A0.IsInvertible) (y : F) :
    A.inverse y-A0.inverse y = A.inverse ((A0-A) (A0.inverse y)) := by
  rw [ContinuousLinearMap.sub_apply,map_sub,hA0.self_apply_inverse,
    hA.inverse_apply_self]

end ShrinkingSpheres
