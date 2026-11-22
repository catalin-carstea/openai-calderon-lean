module

public import Proof.CalderonN.CenterJetCalculus
public import Proof.CalderonN.NormalJointJetEnvelope
public import Proof.CalderonN.NormalCoefficientVelocityJets

import Mathlib.Tactic

/-! The affine stand-in for parallel transport has the true first center jet.
All estimates here are in the unscaled normal coordinates. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev CenterParameters (dim : ℕ) := ℝ × X dim
abbrev FrameOperator (dim : ℕ) := X dim →L[ℝ] X dim

@[expose] def affineCenterFrame (U P : FrameOperator dim) (p : CenterParameters dim) : FrameOperator dim :=
  U+p.1 • P

@[expose] def affineNormalInput (y a : X dim) (U P : FrameOperator dim)
    (p : CenterParameters dim) : X dim × X dim :=
  (y+p.1 • a,affineCenterFrame U P p p.2)

@[expose] def affineNormalPullbackData (d : Data dim) (y a : X dim) (U P : FrameOperator dim)
    (p : CenterParameters dim) : PullbackCoefficientData dim :=
  let b := affineNormalInput y a U P p
  (d.g₁ (d.expMap b),(normalVerticalJacobian d.expMap b.1 b.2).comp (affineCenterFrame U P p))

theorem contDiff_affineCenterFrame (U P : FrameOperator dim) :
    ContDiff ℝ ∞ (affineCenterFrame U P) :=
  contDiff_const.add (contDiff_fst.smul contDiff_const)

theorem contDiff_affineNormalInput (y a : X dim) (U P : FrameOperator dim) :
    ContDiff ℝ ∞ (affineNormalInput y a U P) :=
  (contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk
    ((contDiff_affineCenterFrame U P).clm_apply contDiff_snd)

private lemma norm_fst_smulRight_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) :
    ‖(ContinuousLinearMap.fst ℝ ℝ (X dim)).smulRight v‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun p => by
    rw [ContinuousLinearMap.smulRight_apply,norm_smul,mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_fst_le p) (norm_nonneg _)

theorem norm_iteratedFDeriv_affineCenterFrame_le (U P : FrameOperator dim)
    (v : X dim) (n : ℕ) (A : ℝ) (hU : ‖U‖ ≤ A) (hP : ‖P‖ ≤ A) :
    ‖iteratedFDeriv ℝ n (affineCenterFrame U P) ((0 : ℝ),v)‖ ≤ A := by
  let L := (ContinuousLinearMap.fst ℝ ℝ (X dim)).smulRight P
  exact norm_iteratedFDeriv_affine_envelope_at L U (0,v) n A
    ((norm_nonneg _).trans hU) (by simpa [L] using hU) ((norm_fst_smulRight_le P).trans hP)

theorem norm_iteratedFDeriv_affineNormalInput_le (y a v : X dim) (U P : FrameOperator dim)
    (A : ℝ) (hA : 1 ≤ A) (ha : ‖a‖ ≤ A) (hv : ‖v‖ ≤ 1) (hU : ‖U‖ ≤ A) (hP : ‖P‖ ≤ A)
    (n : ℕ) (hn : 1 ≤ n) (hn3 : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (affineNormalInput y a U P) ((0 : ℝ),v)‖ ≤
      8*‖(ContinuousLinearMap.apply (E := X dim) ℝ (X dim)).flip‖*A+A := by
  let Q := CenterParameters dim
  let x : Q := (0,v)
  let Y (p : Q) := y+p.1 • a
  let S := ContinuousLinearMap.snd ℝ ℝ (X dim)
  let L := (ContinuousLinearMap.apply (E := X dim) ℝ (X dim)).flip
  let F := affineCenterFrame U P
  let W (p : Q) := L (F p) (S p)
  have hY : ContDiff ℝ ∞ Y := contDiff_const.add (contDiff_fst.smul contDiff_const)
  have hF : ContDiff ℝ ∞ F := contDiff_affineCenterFrame U P
  have hW : ContDiff ℝ ∞ W := (L.contDiff.comp hF).clm_apply S.contDiff
  have hN : ‖S‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by
    rw [one_mul]; exact norm_snd_le p
  have hS (i : ℕ) (_hi : i ≤ n) : ‖iteratedFDeriv ℝ i (fun p => S p) x‖ ≤ 1 := by
    simpa only [zero_add] using
      norm_iteratedFDeriv_affine_envelope_at S 0 x i 1 zero_le_one (by simpa [x,S] using hv) hN
  have hWa := norm_iteratedFDeriv_bilinear_envelope_at L F (fun p => S p) x n
    hF.contDiffAt S.contDiff.contDiffAt A 1 (zero_le_one.trans hA) zero_le_one
    (fun i _ => norm_iteratedFDeriv_affineCenterFrame_le U P v i A hU hP) hS
  have hPow : (2:ℝ)^n ≤ 8 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn3).trans_eq (by norm_num)
  have hWn : ‖iteratedFDeriv ℝ n W x‖ ≤ 8*‖L‖*A := by
    simp only [mul_one] at hWa
    exact hWa.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hPow (norm_nonneg L)) (zero_le_one.trans hA))
  have hYn : ‖iteratedFDeriv ℝ n Y x‖ ≤ A := by
    let J := (ContinuousLinearMap.fst ℝ ℝ (X dim)).smulRight a
    have hD : fderiv ℝ Y = fun _ : Q => J := funext fun p => (J.hasFDerivAt.const_add y).fderiv
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [← norm_iteratedFDeriv_fderiv,hD]
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (norm_fst_smulRight_le a).trans ha
    | succ k =>
      simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      exact zero_le_one.trans hA
  change ‖iteratedFDeriv ℝ n (fun p => (Y p,W p)) x‖ ≤ _
  exact (norm_iteratedFDeriv_prod_envelope_at Y W x n hY.contDiffAt hW.contDiffAt hYn hWn).trans
    (max_le (le_add_of_nonneg_left (by positivity)) (le_add_of_nonneg_right (zero_le_one.trans hA)))

end CalderonN
