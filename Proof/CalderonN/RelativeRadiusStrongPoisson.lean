module

public import Proof.CalderonN.RelativeRadiusStrongCoefficient

import Proof.PoissonTaylorDerivative
import Mathlib.Tactic

/-! Uses the released rectangular left-identity estimate to differentiate
the genuine fixed-ball replacement with respect to relative radius. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem norm_deriv_of_relative_affine_residual_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : ℝ → V) (A1 : V) (hA : DifferentiableAt ℝ A 0) (r Q : ℝ) (hr : 0 ≤ r)
    (hQ : ‖fderiv ℝ (fun t => A t - ((1+t)*r) • A1) 0‖ ≤ Q) :
    ‖fderiv ℝ A 0‖ ≤ Q + r*‖A1‖ := by
  have ha : HasDerivAt (fun t : ℝ => ((1+t)*r) • A1) (r • A1) 0 := by
    have h := (((hasDerivAt_id (0:ℝ)).const_add 1).mul_const r).smul_const A1
    simpa only [id_eq,one_mul] using h
  have hD : deriv (fun t => A t - ((1+t)*r) • A1) 0 = deriv A 0 - r • A1 :=
    (hA.hasDerivAt.sub ha).deriv
  rw [← norm_deriv_eq_norm_fderiv,hD] at hQ
  rw [← norm_deriv_eq_norm_fderiv,← sub_add_cancel (deriv A 0) (r • A1)]
  exact (norm_add_le _ _).trans
    (add_le_add hQ (by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]))

/-- The relative-radius derivative of the first-order Poisson remainder
on a flat harmonic lift has the same quadratic gain as the point estimate. -/
theorem norm_relativeRadius_poisson_taylor_derivative_le
    (a : ℝ × X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (J : Set (X dim)) (hJ : IsCompact J) (hSupp : ∀ t z, z ∉ J → a (t,z) = 0)
    (F0 F1 : SmoothCoefficientMatrix dim 2)
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P0 : H →L[ℝ] BallSobolev dim 2)
    (hFlat : (fullBallDivergenceL 0 F0).comp P0 = 0)
    (r C D L Q B₁ B₂ V : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hV : 0 ≤ V)
    (hI₀ : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (hInv₀ : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ C)
    (hFull₁ : ‖fullBallDivergenceL 0 F1‖ ≤ L)
    (hStrong₁ : ‖strongDirichletOperator fixedSobolevCalculus 0 F1‖ ≤ V)
    (hPoint : let F := commonSupportMatrixFamily 2 a ha J hJ hSupp 0
      let A := strongDirichletOperator fixedSobolevCalculus 0 F
      let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
      A.IsInvertible ∧ ‖A.inverse‖ ≤ C ∧ ‖A-A0‖ ≤ D*r ∧
      ‖fullBallDivergenceL 0 F-fullBallDivergenceL 0 F0-r • fullBallDivergenceL 0 F1‖ ≤ Q*r^2)
    (hRadius : let F := commonSupportMatrixFamily 2 a ha J hJ hSupp
      ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t) -
        ((1+t)*r) • strongDirichletOperator fixedSobolevCalculus 0 F1) 0‖ ≤ B₁*r^2 ∧
      ‖fderiv ℝ (fun t => fullBallDivergenceL 0 (F t) -
        ((1+t)*r) • fullBallDivergenceL 0 F1) 0‖ ≤ B₂*r^2) :
    let F := commonSupportMatrixFamily 2 a ha J hJ hSupp
    let j := (strongDirichletSubmodule dim 0).toSubmodule.subtypeL
    let I₀ := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
    let P1 := -(j.comp (I₀.comp ((fullBallDivergenceL 0 F1).comp P0)))
    ‖fderiv ℝ (fun t => (ballPoissonOperatorL 0 (F t)).comp P0-P0-((1+t)*r) • P1) 0‖ ≤
      C * (B₂+(B₁+V)*C*L+D*C*L+(B₁+V)*C*(Q+C*D*L)) * ‖P0‖ * r^2 := by
  let F := commonSupportMatrixFamily 2 a ha J hJ hSupp
  let A := fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
  let A1 := strongDirichletOperator fixedSobolevCalculus 0 F1
  let T := fun t => fullBallDivergenceL 0 (F t)
  let T0 := fullBallDivergenceL 0 F0
  let L1 := fullBallDivergenceL 0 F1
  let T1 := fun t : ℝ => (1+t) • L1
  let S := fun t => (A t).inverse.comp ((T t).comp P0)-r • A0.inverse.comp ((T1 t).comp P0)
  let j := (strongDirichletSubmodule dim 0).toSubmodule.subtypeL
  let U := {t : ℝ | (A t).IsInvertible}
  have hA : ContDiff ℝ ∞ A :=
    contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha J hJ hSupp
  have hT : ContDiff ℝ ∞ T := contDiff_fullBallDivergence_family 0 a ha J hJ hSupp
  have hT1d : HasDerivAt T1 L1 0 := by
    simpa only [T1,id_eq,one_smul] using (((hasDerivAt_id (0:ℝ)).const_add 1).smul_const L1)
  have hT1 : DifferentiableAt ℝ T1 0 := hT1d.differentiableAt
  have hU : IsOpen U := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hA.continuous
  have hU₀ : (0 : ℝ) ∈ U := hPoint.1
  have hInv (t : ℝ) (ht : t ∈ U) : (A t).IsInvertible := ht
  have hI : ContDiffOn ℝ ∞ (fun t => (A t).inverse) U :=
    contDiffOn_banachInverseFamily A U hA.contDiffOn hInv
  have hS : ContDiffAt ℝ ∞ S 0 := by
    have hIa := (hI 0 hU₀).contDiffAt (hU.mem_nhds hU₀)
    have hT₀ := hT.contDiffAt (x := (0 : ℝ))
    have hT₁ : ContDiff ℝ ∞ T1 := (contDiff_const.add contDiff_id).smul contDiff_const
    exact (hIa.clm_comp (hT₀.clm_comp contDiffAt_const)).sub
      (contDiffAt_const.clm_comp (hT₁.contDiffAt.clm_comp contDiffAt_const) |>.const_smul r)
  have hDA : ‖fderiv ℝ A 0‖ ≤ (B₁+V)*r := by
    have h := norm_deriv_of_relative_affine_residual_le A A1 (hA.differentiable (by simp) 0)
      r (B₁*r^2) hr hRadius.1
    have hSq : r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hr1 hr]
    calc
      _ ≤ B₁*r^2+r*‖A1‖ := h
      _ ≤ B₁*r+r*V := add_le_add (mul_le_mul_of_nonneg_left hSq hB₁)
        (mul_le_mul_of_nonneg_left hStrong₁ hr)
      _ = _ := by ring
  have hAffine (t : ℝ) : r • T1 t = ((1+t)*r) • L1 := by
    change r • ((1+t) • L1) = _
    rw [smul_smul,mul_comm]
  have hQ₁ : ‖fderiv ℝ (fun t => T t-T0-r • T1 t) 0‖ ≤ B₂*r^2 := by
    have hFun : (fun t => T t-T0-r • T1 t) = fun t => (T t-((1+t)*r) • L1)-T0 := by
      funext t
      rw [hAffine]
      abel
    rw [hFun,fderiv_sub_const]
    exact hRadius.2
  have hQd : DifferentiableAt ℝ (fun t => T t-T0-r • T1 t) 0 :=
    ((hT.differentiable (by simp) 0).sub_const T0).sub (hT1.const_smul r)
  have hPt : ‖S 0‖ ≤ (C*(Q+C*D*L)*‖P0‖)*r^2 := by
    let R := T 0 - T0 - r • L1
    let G := (A 0).inverse - A0.inverse
    have hR : ‖R‖ ≤ Q*r^2 := hPoint.2.2.2
    have hG : ‖G‖ ≤ C*(D*r)*C := ShrinkingSpheres.norm_inverse_sub_le (A 0) A0 hPoint.1 hI₀
      C C (D*r) hC hC (mul_nonneg hD hr) hPoint.2.1 hInv₀ hPoint.2.2.1
    have hEq : S 0 = (A 0).inverse.comp (R.comp P0) + r • G.comp (L1.comp P0) := by
      apply ContinuousLinearMap.ext
      intro x
      have hx : T0 (P0 x) = 0 := congrArg (fun m : H →L[ℝ] BallSobolev dim 0 => m x) hFlat
      simp only [S,T1,R,G,add_zero,one_smul,add_apply,sub_apply,smul_apply,
        ContinuousLinearMap.comp_apply,map_sub,map_smul,hx,sub_zero]
      module
    have hLeft : ‖(A 0).inverse.comp (R.comp P0)‖ ≤ C*((Q*r^2)*‖P0‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        gcongr
        exact hPoint.2.1
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right hR (norm_nonneg _)))
    have hRight : ‖r • G.comp (L1.comp P0)‖ ≤ r*((C*(D*r)*C)*(L*‖P0‖)) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
      apply mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_) hr
      exact mul_le_mul hG ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right hFull₁ (norm_nonneg _))) (norm_nonneg _) (by positivity)
    rw [hEq]
    exact ((norm_add_le _ _).trans (add_le_add hLeft hRight)).trans_eq (by ring)
  have h1 : ‖T1 0‖ ≤ L := by simpa only [T1,add_zero,one_smul] using hFull₁
  have hd1 : ‖fderiv ℝ T1 0‖ ≤ L := by rwa [← norm_deriv_eq_norm_fderiv,hT1d.deriv]
  have hBound := ShrinkingSpheres.norm_poisson_taylor_remainder_derivative_le
    A A0 T T1 T0 P0 S r 0 U hU hU₀ (hA.differentiable (by simp) 0) hT1 hQd
    (hS.differentiableAt (by simp)) hInv hI₀ hFlat (fun _ _ => rfl)
    C C (B₁+V) D L L B₂ (C*(Q+C*D*L)*‖P0‖) hr hr1 hC hC
    (add_nonneg hB₁ hV) hD hL hL hB₂ (by positivity)
    hPoint.2.1 hInv₀ hDA hPoint.2.2.1 h1 hd1 hQ₁ hPt
  let P1 := -(j.comp (A0.inverse.comp (L1.comp P0)))
  have hEq : (fun t => (ballPoissonOperatorL 0 (F t)).comp P0-P0-((1+t)*r) • P1) =
      fun t => -(j.comp (S t)) := by
    funext t
    apply ContinuousLinearMap.ext
    intro x
    have he : S t x = (A t).inverse (T t (P0 x)) -
        ((1+t)*r) • A0.inverse (L1 (P0 x)) := by
      simp only [S,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,T1,map_smul,smul_smul,mul_comm r (1+t)]
    have hp : P1 x = -j (A0.inverse (L1 (P0 x))) := rfl
    have hb : ballPoissonOperatorL 0 (F t) (P0 x) = P0 x - j ((A t).inverse (T t (P0 x))) := rfl
    change ballPoissonOperatorL 0 (F t) (P0 x)-P0 x-((1+t)*r) • P1 x = -j (S t x)
    rw [he,hp,hb,map_sub,map_smul]
    module
  change ‖fderiv ℝ (fun t => (ballPoissonOperatorL 0 (F t)).comp P0-P0-((1+t)*r) • P1) 0‖ ≤ _
  rw [hEq]
  have hDeriv := (hS.differentiableAt (by simp)).hasDerivAt
  let hComp := ContinuousLinearMap.compL ℝ H (StrongDirichletSpace dim 0) (BallSobolev dim 2) j
  have hComp' : HasDerivAt (fun t => j.comp (S t)) (j.comp (deriv S 0)) 0 :=
    hComp.hasFDerivAt.comp_hasDerivAt 0 hDeriv
  rw [← norm_deriv_eq_norm_fderiv]
  change ‖deriv (fun t => -(j.comp (S t))) 0‖ ≤ _
  change ‖deriv (-(fun t => j.comp (S t))) 0‖ ≤ _
  rw [deriv.neg,hComp'.deriv,norm_neg]
  have hj : ‖j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    rw [one_mul]
    exact le_rfl
  have h_le := (ContinuousLinearMap.opNorm_comp_le j (deriv S 0)).trans
    ((mul_le_mul_of_nonneg_right hj (norm_nonneg _)).trans_eq (one_mul _))
  rw [norm_deriv_eq_norm_fderiv] at h_le
  exact (h_le.trans hBound).trans_eq (by ring)

end CalderonN
