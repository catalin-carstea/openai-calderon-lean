import Proof.FiniteJetBudgetAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma norm_iteratedFDeriv_affine_clm_positive (L : P →L[ℝ] E) (b : E) (p : P) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun q => b+L q) p‖ = if n=1 then ‖L‖ else 0 := by
  have hD : fderiv ℝ (fun q => b+L q) = fun _ => L := by
    funext q
    have hh := (hasFDerivAt_const b q).fun_add L.hasFDerivAt
    simpa only [Pi.add_apply,zero_add] using hh.fderiv
  cases n with
  | zero => omega
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv,hD]
    cases n with
    | zero => simp only [norm_iteratedFDeriv_zero,ite_true]
    | succ n => simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]

/-- Rescaling the center by beta inverse removes the correct derivative
    powers. The scalar prefactor removes the value's fixed weight s. -/
theorem norm_iteratedFDeriv_affine_rescaled_weighted_le
    (L : P →L[ℝ] E) (b : E) (p : P) (g : E → F)
    (hg : ContDiffAt ℝ ∞ g (b+L p)) (N s : ℕ) (β C : ℝ)
    (hβ : 1 ≤ β) (hC : 0 ≤ C) (hL : ‖L‖ ≤ β⁻¹)
    (hG : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j g (b+L p)‖ ≤ C*β^(j+s))
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun q => (β^s)⁻¹ • g (b+L q)) p‖ ≤ (N.factorial:ℝ)*C := by
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  have hInner : ContDiffAt ℝ ∞ (fun q => b+L q) p := contDiffAt_const.add L.contDiff.contDiffAt
  have hInnerJets (j : ℕ) (hj : 1 ≤ j) (_hjn : j ≤ n) :
      ‖iteratedFDeriv ℝ j (fun q => b+L q) p‖ ≤ (β⁻¹)^j := by
    rw [norm_iteratedFDeriv_affine_clm_positive L b p j hj]
    split_ifs with he
    · subst j
      simpa only [pow_one] using hL
    · positivity
  have hOuter (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j g (b+L p)‖ ≤ C*β^(n+s) :=
    (hG j (hj.trans hn)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hβ (by omega)) hC)
  have hh := norm_iteratedFDeriv_comp_at_bound (fun q => b+L q) g p hInner hg n (C*β^(n+s)) β⁻¹ hOuter hInnerJets
  have hSmooth : ContDiffAt ℝ ∞ (fun q => g (b+L q)) p := hg.comp p hInner
  rw [norm_iteratedFDeriv_const_smul_at _ p hSmooth,abs_of_nonneg (by positivity : 0 ≤ (β^s)⁻¹)]
  calc
    _ ≤ (β^s)⁻¹*((n.factorial:ℝ)*(C*β^(n+s))*(β⁻¹)^n) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = (n.factorial:ℝ)*C := by
      rw [pow_add,inv_pow]
      field_simp
      <;> ring
    _ ≤ (N.factorial:ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hn) hC

end ShrinkingSpheres
