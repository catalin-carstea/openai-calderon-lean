import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma iteratedFDeriv_fixed_add_positive (f : P → V) (c : V) (p : P) (n : ℕ) (hn : 1 ≤ n) :
    iteratedFDeriv ℝ n (fun q => c+f q) p = iteratedFDeriv ℝ n f p := by
  have hD : fderiv ℝ (fun q => c+f q) = fderiv ℝ f := by
    funext q
    exact fderiv_const_add c
  cases n with
  | zero => omega
  | succ k =>
    conv_lhs => rw [iteratedFDeriv_succ_eq_comp_right]
    conv_rhs => rw [iteratedFDeriv_succ_eq_comp_right]
    rw [hD]

/-- The exact affine identity transports every positive derivative even for
    a merely arbitrary family; no extra smoothness interface must be matched. -/
theorem iteratedFDeriv_affine_family_positive_eq
    (A A1 D : P → V) (A00 A0 : V) (r : ℝ) (p : P) (n : ℕ) (hn : 1 ≤ n)
    (hFamily : ∀ q,A q = A00+r • A1 q+D q) :
    iteratedFDeriv ℝ n (fun q => A q-A0-r • A1 q) p = iteratedFDeriv ℝ n D p := by
  have hEq : (fun q => A q-A0-r • A1 q) = fun q => (A00-A0)+D q := by
    funext q
    rw [hFamily]
    module
  rw [hEq]
  exact iteratedFDeriv_fixed_add_positive D (A00-A0) p n hn

end ShrinkingSpheres
