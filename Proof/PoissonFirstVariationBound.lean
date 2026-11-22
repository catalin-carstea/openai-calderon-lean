module

public import Proof.InversePerturbation
public import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres

/-- A quantitative resolvent estimate with explicitly shared inverse witnesses. -/
theorem norm_inverse_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A A0 : E →L[ℝ] F) (hA : A.IsInvertible) (hA0 : A0.IsInvertible)
    (C C0 D : ℝ) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) (hD : 0 ≤ D)
    (hInv : ‖A.inverse‖ ≤ C) (hInv0 : ‖A0.inverse‖ ≤ C0) (hDiff : ‖A-A0‖ ≤ D) :
    ‖A.inverse-A0.inverse‖ ≤ C*D*C0 := by
  have hEq : A.inverse-A0.inverse = A.inverse.comp ((A0-A).comp A0.inverse) := by
    ext y
    exact inverse_sub_inverse_apply A A0 hA hA0 y
  rw [hEq]
  calc
    _ ≤ ‖A.inverse‖*(‖A0-A‖*‖A0.inverse‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C*(D*C0) := by rw [norm_sub_rev A0 A];gcongr
    _ = _ := by ring

/-- A second-order bulk Poisson remainder from an affine operator model.
    This estimate is valid for the actual canonical inverses; differentiability
    of an arbitrarily extended parameter family is not a premise. -/
theorem norm_poisson_first_variation_remainder_le
    {Z E F H : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (j : Z →L[ℝ] E) (A A0 : Z →L[ℝ] F) (T T0 T1 : E →L[ℝ] F) (P0 : H →L[ℝ] E)
    (hA : A.IsInvertible) (hA0 : A0.IsInvertible)
    (hFlat : T0.comp P0 = 0) (hj : ‖j‖ ≤ 1)
    (r C C0 D L Q : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hInv : ‖A.inverse‖ ≤ C) (hInv0 : ‖A0.inverse‖ ≤ C0)
    (hDiff : ‖A-A0‖ ≤ D*r) (hT1 : ‖T1‖ ≤ L)
    (hTaylor : ‖T-T0-r • T1‖ ≤ Q*r^2) :
    ‖(P0-j.comp (A.inverse.comp (T.comp P0)))-P0-
      r • (-(j.comp (A0.inverse.comp (T1.comp P0))))‖ ≤
      C*(Q+C0*D*L)*‖P0‖*r^2 := by
  have hInvDiff : ‖A.inverse-A0.inverse‖ ≤ C*(D*r)*C0 :=
    norm_inverse_sub_le A A0 hA hA0 C C0 (D*r) hC hC0 (mul_nonneg hD hr) hInv hInv0 hDiff
  let R := T-T0-r • T1
  have hEq : (P0-j.comp (A.inverse.comp (T.comp P0)))-P0-
      r • (-(j.comp (A0.inverse.comp (T1.comp P0)))) =
      -(j.comp (A.inverse.comp (R.comp P0)))-
        r • (j.comp ((A.inverse-A0.inverse).comp (T1.comp P0))) := by
    ext f
    have hZero : T0 (P0 f) = 0 := congrArg (fun B : H →L[ℝ] F => B f) hFlat
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,R,map_sub,map_smul,hZero,map_zero,sub_zero]
    module
  have hFirst : ‖j.comp (A.inverse.comp (R.comp P0))‖ ≤ C*(Q*r^2)*‖P0‖ := by
    calc
      _ ≤ ‖j‖*(‖A.inverse‖*(‖R‖*‖P0‖)) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ 1*(C*((Q*r^2)*‖P0‖)) := by gcongr
      _ = _ := by ring
  have hSecond : ‖j.comp ((A.inverse-A0.inverse).comp (T1.comp P0))‖ ≤
      (C*(D*r)*C0)*L*‖P0‖ := by
    calc
      _ ≤ ‖j‖*(‖A.inverse-A0.inverse‖*(‖T1‖*‖P0‖)) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ 1*((C*(D*r)*C0)*(L*‖P0‖)) := by gcongr
      _ = _ := by ring
  rw [hEq]
  calc
    _ ≤ ‖-(j.comp (A.inverse.comp (R.comp P0)))‖+
        ‖r • (j.comp ((A.inverse-A0.inverse).comp (T1.comp P0)))‖ := norm_sub_le _ _
    _ = ‖j.comp (A.inverse.comp (R.comp P0))‖+
        r*‖j.comp ((A.inverse-A0.inverse).comp (T1.comp P0))‖ := by
      rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    _ ≤ C*(Q*r^2)*‖P0‖+r*((C*(D*r)*C0)*L*‖P0‖) :=
      add_le_add hFirst (mul_le_mul_of_nonneg_left hSecond hr)
    _ = _ := by ring

end ShrinkingSpheres
