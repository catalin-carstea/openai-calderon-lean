module

public import Proof.CalderonN.ConnectionSecondBounds
public import Proof.CalderonN.BackgroundBudgets

import Mathlib.Tactic

/-! Adapted from `UniformSecondConnection` in the checked Proposition 5.3 release. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

def secondConnectionBudget (dim : ℕ) (K M₁ M₂ M₃ : ℝ) : ℝ :=
  (dim:ℝ)^3*((3*(dim:ℝ))*(K*M₃+2*((dim:ℝ)^2*K^2*M₁)*M₂+((dim:ℝ)^2*((dim:ℝ)^2*((2*(dim:ℝ)^2)*K^3*M₁^2+K^2*M₂)))*M₁))

/-- Full operator control of the actual second derivative of the connection. -/
theorem Elliptic.connection_second_operator_bound {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X dim)} (hy : y ∈ Ω)
    (M₁ M₂ M₃ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hD : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (hD₂ : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂)
    (hD₃ : ∀ i j,‖iteratedFDeriv ℝ 3 (fun x => g x i j) y‖ ≤ M₃) :
    ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) y‖ ≤ secondConnectionBudget dim K M₁ M₂ M₃ := by
  let C := (3*(dim:ℝ))*(K*M₃+2*((dim:ℝ)^2*K^2*M₁)*M₂+((dim:ℝ)^2*((dim:ℝ)^2*((2*(dim:ℝ)^2)*K^3*M₁^2+K^2*M₂)))*M₁)
  have hΓ (i j k : (I dim)) : ContDiffAt ℝ ∞ (fun x => christoffel g x k i j) y :=
    (h.contDiffOn_christoffel hΩ hK k i j).contDiffAt (hΩ.mem_nhds hy)
  let F (i j k : (I dim)) (x : (X dim)) := christoffel g x k i j • coordinateBilinearAtom i j k
  have hF (i j k : (I dim)) : ContDiffAt ℝ 2 (F i j k) y :=
    ((hΓ i j k).smul contDiffAt_const).of_le (by simp)
  have hNormScalar (f : (X dim) → ℝ) :
      ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fderiv ℝ f) y‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
  have hNormConnection : ‖iteratedFDeriv ℝ 2 (connectionBilinear g) y‖ =
      ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) y‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
  have hTerm (i j k : (I dim)) : ‖iteratedFDeriv ℝ 2 (F i j k) y‖ ≤ C := by
    have hh := norm_iteratedFDeriv_smul_const_le (hΓ i j k) (coordinateBilinearAtom i j k) 2
    have hEntry := h.christoffel_second_fderiv_bound hΩ hK hy M₁ M₂ M₃ hM₁ hM₂ hM₃ hD hD₂ hD₃ k i j
    exact hh.trans ((mul_le_mul (coordinateBilinearAtom_norm_le_one i j k)
      (by simpa only [hNormScalar,C] using hEntry) (norm_nonneg _) zero_le_one).trans_eq (one_mul C))
  have hFun : connectionBilinear g = fun x => ∑ i,∑ j,∑ k,F i j k x := rfl
  have h2 (i j : (I dim)) :
      iteratedFDeriv ℝ 2 (fun x => ∑ k,F i j k x) y = ∑ k,iteratedFDeriv ℝ 2 (F i j k) y :=
    iteratedFDeriv_fun_sum_apply (fun k _ => hF i j k)
  have h1 (i : (I dim)) :
      iteratedFDeriv ℝ 2 (fun x => ∑ j,∑ k,F i j k x) y =
        ∑ j,iteratedFDeriv ℝ 2 (fun x => ∑ k,F i j k x) y :=
    iteratedFDeriv_fun_sum_apply (fun j _ => ContDiffAt.sum (fun k _ => hF i j k))
  rw [← hNormConnection,hFun,
    iteratedFDeriv_fun_sum_apply (fun i _ => ContDiffAt.sum
      (fun j _ => ContDiffAt.sum (fun k _ => hF i j k)))]
  change ‖∑ i,iteratedFDeriv ℝ 2 (fun x => ∑ j,∑ k,F i j k x) y‖ ≤ (dim:ℝ)^3*C
  have hRes (i : (I dim)) : iteratedFDeriv ℝ 2 (fun x => ∑ j,∑ k,F i j k x) y =
      ∑ j,∑ k,iteratedFDeriv ℝ 2 (F i j k) y := by
    rw [h1 i]
    exact Finset.sum_congr rfl (fun j _ => h2 i j)
  have hOuter : (∑ i,iteratedFDeriv ℝ 2 (fun x => ∑ j,∑ k,F i j k x) y) =
      ∑ i,∑ j,∑ k,iteratedFDeriv ℝ 2 (F i j k) y :=
    Finset.sum_congr rfl (fun i _ => hRes i)
  rw [hOuter]
  exact norm_coordinate_triple_sum_le (fun i j k => iteratedFDeriv ℝ 2 (F i j k) y) C hTerm

def backgroundSecondConnectionBudget (dim : ℕ) {m : ℕ} (hm : 3 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  secondConnectionBudget dim K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩|

/-- Uniform second-connection control from the frozen background budgets. -/
theorem Background.connection_second_derivative_budget {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ}
    {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m) {y : (X dim)} (hy : y ∈ Ω) :
    ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) y‖ ≤ backgroundSecondConnectionBudget dim hm K M := by
  exact h.1.connection_second_operator_bound hΩ hK hy
    |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩|
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (fun i j => (h.reference_fderiv_bound (by omega) hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_second_fderiv_bound (by omega) hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_jet_bound ⟨3,by omega⟩ hy i j).trans (le_abs_self _))

end CalderonN
