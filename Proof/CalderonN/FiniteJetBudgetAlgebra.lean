module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Proof.CalderonN.FiniteJetBoundCalculus

/-! From FiniteJetBudgetAlgebra in the checked Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma norm_iteratedFDeriv_add_at_le (f g : P → V) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => f p+g p) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖ := by
  change ‖iteratedFDeriv ℝ n (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.of_le (by simp)) (hg.of_le (by simp))]
  exact norm_add_le _ _

lemma norm_iteratedFDeriv_sub_at_le (f g : P → V) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => f p-g p) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖ := by
  change ‖iteratedFDeriv ℝ n (f-g) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (hf.of_le (by simp)) (hg.of_le (by simp))]
  exact norm_sub_le _ _

lemma norm_iteratedFDeriv_const_smul_at (f : P → V) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (c : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => c • f p) x‖ = |c| * ‖iteratedFDeriv ℝ n f x‖ := by
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by simp)),norm_smul,Real.norm_eq_abs]

lemma norm_iteratedFDeriv_neg_at (f : P → V) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => -f p) x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  have h := norm_iteratedFDeriv_const_smul_at f x hf (-1) n
  simpa only [neg_one_smul,abs_neg,abs_one,one_mul] using h

theorem norm_iteratedFDeriv_difference_of_affine_remainder_le
    (A A1 : P → V) (A0 : V) (x : P) (hA : ContDiffAt ℝ ∞ A x) (hA1 : ContDiffAt ℝ ∞ A1 x)
    (n : ℕ) (r C1 CQ : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC1 : 0 ≤ C1) (hCQ : 0 ≤ CQ)
    (hFirst : ‖iteratedFDeriv ℝ n A1 x‖ ≤ C1)
    (hRem : ‖iteratedFDeriv ℝ n (fun p => A p-A0-r • A1 p) x‖ ≤ CQ*r^2) :
    ‖iteratedFDeriv ℝ n (fun p => A p-A0) x‖ ≤ (C1+CQ)*r := by
  let R := fun p => A p-A0-r • A1 p
  have hR : ContDiffAt ℝ ∞ R x := (hA.sub contDiffAt_const).sub (hA1.const_smul r)
  have hEq : (fun p => A p-A0) = fun p => r • A1 p+R p := by
    funext p
    dsimp only [R]
    module
  rw [hEq]
  have hh := norm_iteratedFDeriv_add_at_le (fun p => r • A1 p) R x (hA1.const_smul r) hR n
  rw [norm_iteratedFDeriv_const_smul_at A1 x hA1 r n,abs_of_nonneg hr] at hh
  have hrr : r^2 ≤ r := by nlinarith
  exact hh.trans ((add_le_add (mul_le_mul_of_nonneg_left hFirst hr) hRem).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hrr hCQ]))

lemma norm_iteratedFDeriv_operator_postcomp_fixed_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (A : P → E →L[ℝ] F) (x : P) (hA : ContDiffAt ℝ ∞ A x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => L.comp (A p)) x‖ ≤ ‖L‖*‖iteratedFDeriv ℝ n A x‖ := by
  let T := (ContinuousLinearMap.compL ℝ E F G) L
  have hT : ‖T‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro B
    exact ContinuousLinearMap.opNorm_comp_le _ _
  exact (norm_iteratedFDeriv_clm_comp_le T A x hA n).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

lemma norm_iteratedFDeriv_operator_precomp_fixed_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : P → F →L[ℝ] G) (R : E →L[ℝ] F) (x : P) (hA : ContDiffAt ℝ ∞ A x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => (A p).comp R) x‖ ≤ ‖R‖*‖iteratedFDeriv ℝ n A x‖ := by
  let T := (ContinuousLinearMap.compL ℝ E F G).flip R
  have hT : ‖T‖ ≤ ‖R‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro B
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)
  exact (norm_iteratedFDeriv_clm_comp_le T A x hA n).trans
    (mul_le_mul_of_nonneg_right hT (norm_nonneg _))

end ShrinkingSpheres
