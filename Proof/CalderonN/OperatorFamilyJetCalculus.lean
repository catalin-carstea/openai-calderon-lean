module

public import Proof.CalderonN.BilinearFamilyJetBounds
public import Proof.CalderonN.FiniteJetBoundCalculus

/-! From OperatorFamilyJetCalculus in the checked Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E F G H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

def operatorSandwichL (L : F →L[ℝ] G) (R : H →L[ℝ] E) :
    (E →L[ℝ] F) →L[ℝ] (H →L[ℝ] G) :=
  ((ContinuousLinearMap.compL ℝ H F G) L).comp
    ((ContinuousLinearMap.compL ℝ H E F).flip R)

lemma norm_operatorSandwichL_le (L : F →L[ℝ] G) (R : H →L[ℝ] E) :
    ‖operatorSandwichL L R‖ ≤ ‖L‖*‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  change ‖L.comp (A.comp R)‖ ≤ _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans_eq (by ring))

theorem norm_iteratedFDeriv_operator_sandwich_le
    (L : F →L[ℝ] G) (R : H →L[ℝ] E) (A : P → E →L[ℝ] F)
    (x : P) (hA : ContDiffAt ℝ ∞ A x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p => L.comp ((A p).comp R)) x‖ ≤
      ‖L‖*‖R‖*‖iteratedFDeriv ℝ n A x‖ :=
  (norm_iteratedFDeriv_clm_comp_le (operatorSandwichL L R) A x hA n).trans
    (mul_le_mul_of_nonneg_right (norm_operatorSandwichL_le L R) (norm_nonneg _))

theorem norm_iteratedFDeriv_operator_comp_common_bound
    (A : P → F →L[ℝ] G) (B : P → E →L[ℝ] F) (x : P)
    (hA : ContDiffAt ℝ ∞ A x) (hB : ContDiffAt ℝ ∞ B x)
    (N : ℕ) (CA CB : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hAJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j A x‖ ≤ CA)
    (hBJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j B x‖ ≤ CB)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => (A p).comp (B p)) x‖ ≤ 2^N*CA*CB := by
  have hh := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.compL ℝ E F G)
    A B x hA hB N CA CB hCA hCB hAJets hBJets n hn
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ E F G)
      (by positivity : 0 ≤ (2:ℝ)^N)) hCA) hCB).trans_eq (by ring))

lemma norm_iteratedFDeriv_const_le (c : F) (x : P) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun _ : P => c) x‖ ≤ ‖c‖ := by
  by_cases hn : n = 0
  · subst n
    simp only [norm_iteratedFDeriv_zero]
    exact le_rfl
  · rw [iteratedFDeriv_const_of_ne hn,Pi.zero_apply,norm_zero]
    exact norm_nonneg c

lemma norm_iteratedFDeriv_const_sub_le
    (f : P → F) (x : P) (hf : ContDiffAt ℝ ∞ f x) (c : F) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => c-f y) x‖ ≤ ‖c‖+‖iteratedFDeriv ℝ n f x‖ := by
  change ‖iteratedFDeriv ℝ n ((fun _ : P => c)-f) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (f:=fun _ : P => c) (g:=f) contDiffAt_const (hf.of_le (by simp))]
  exact (norm_sub_le _ _).trans (add_le_add (norm_iteratedFDeriv_const_le c x n) le_rfl)

end ShrinkingSpheres
