import Proof.ConnectionThirdBounds
import Proof.UniformNormalJacobiBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def thirdConnectionBudget (K M₁ M₂ M₃ M₄ : ℝ) : ℝ :=
  27*(9*(K*M₄+3*(9*K^2*M₁)*M₃+3*(9*(162*K^3*M₁^2+9*K^2*M₂))*M₂+(9*(K^2*M₃+4*K*(9*K^2*M₁)*M₂+(2*K*(9*(162*K^3*M₁^2+9*K^2*M₂))+2*(9*K^2*M₁)^2)*M₁))*M₁))

/-- Full operator control of the actual third derivative of the connection. -/
theorem Elliptic.connection_third_operator_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (M₁ M₂ M₃ M₄ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (hD : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (hD₂ : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂)
    (hD₃ : ∀ i j,‖iteratedFDeriv ℝ 3 (fun x => g x i j) y‖ ≤ M₃)
    (hD₄ : ∀ i j,‖iteratedFDeriv ℝ 4 (fun x => g x i j) y‖ ≤ M₄) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) y‖ ≤ thirdConnectionBudget K M₁ M₂ M₃ M₄ := by
  let C := 9*(K*M₄+3*(9*K^2*M₁)*M₃+3*(9*(162*K^3*M₁^2+9*K^2*M₂))*M₂+(9*(K^2*M₃+4*K*(9*K^2*M₁)*M₂+(2*K*(9*(162*K^3*M₁^2+9*K^2*M₂))+2*(9*K^2*M₁)^2)*M₁))*M₁)
  have hΓ (i j k : I) : ContDiffAt ℝ ∞ (fun x => christoffel g x k i j) y :=
    (h.contDiffOn_christoffel hΩ hK k i j).contDiffAt (hΩ.mem_nhds hy)
  let F (i j k : I) (x : X) := christoffel g x k i j • coordinateBilinearAtom i j k
  have hF (i j k : I) : ContDiffAt ℝ 3 (F i j k) y :=
    ((hΓ i j k).smul contDiffAt_const).of_le (by simp)
  have hNormScalar (f : X → ℝ) :
      ‖iteratedFDeriv ℝ 3 f y‖ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y‖ := by
    exact norm_iteratedFDeriv_three_eq_nested _ _
  have hNormConnection : ‖iteratedFDeriv ℝ 3 (connectionBilinear g) y‖ =
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) y‖ := by
    exact norm_iteratedFDeriv_three_eq_nested _ _
  have hTerm (i j k : I) : ‖iteratedFDeriv ℝ 3 (F i j k) y‖ ≤ C := by
    have hh := norm_iteratedFDeriv_smul_const_le (hΓ i j k) (coordinateBilinearAtom i j k) 3
    have hEntry := h.christoffel_third_fderiv_bound hΩ hK hy M₁ M₂ M₃ M₄ hM₁ hM₂ hM₃ hM₄ hD hD₂ hD₃ hD₄ k i j
    exact hh.trans ((mul_le_mul (coordinateBilinearAtom_norm_le_one i j k)
      (by simpa only [hNormScalar,C] using hEntry) (norm_nonneg _) zero_le_one).trans_eq (one_mul C))
  have hFun : connectionBilinear g = fun x => ∑ i,∑ j,∑ k,F i j k x := rfl
  have h2 (i j : I) :
      iteratedFDeriv ℝ 3 (fun x => ∑ k,F i j k x) y = ∑ k,iteratedFDeriv ℝ 3 (F i j k) y :=
    iteratedFDeriv_fun_sum_apply (fun k _ => hF i j k)
  have h1 (i : I) :
      iteratedFDeriv ℝ 3 (fun x => ∑ j,∑ k,F i j k x) y =
        ∑ j,iteratedFDeriv ℝ 3 (fun x => ∑ k,F i j k x) y :=
    iteratedFDeriv_fun_sum_apply (fun j _ => ContDiffAt.sum (fun k _ => hF i j k))
  rw [← hNormConnection,hFun,
    iteratedFDeriv_fun_sum_apply (fun i _ => ContDiffAt.sum
      (fun j _ => ContDiffAt.sum (fun k _ => hF i j k)))]
  change ‖∑ i,iteratedFDeriv ℝ 3 (fun x => ∑ j,∑ k,F i j k x) y‖ ≤ 27*C
  have hRes (i : I) : iteratedFDeriv ℝ 3 (fun x => ∑ j,∑ k,F i j k x) y =
      ∑ j,∑ k,iteratedFDeriv ℝ 3 (F i j k) y := by
    rw [h1 i]
    exact Finset.sum_congr rfl (fun j _ => h2 i j)
  have hOuter : (∑ i,iteratedFDeriv ℝ 3 (fun x => ∑ j,∑ k,F i j k x) y) =
      ∑ i,∑ j,∑ k,iteratedFDeriv ℝ 3 (F i j k) y :=
    Finset.sum_congr rfl (fun i _ => hRes i)
  rw [hOuter]
  exact norm_fin3_triple_sum_le (fun i j k => iteratedFDeriv ℝ 3 (F i j k) y) C hTerm

def backgroundThirdConnectionBudget {m : ℕ} (hm : 4 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  thirdConnectionBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩| |M ⟨4,by omega⟩|

/-- Uniform third-connection control from the frozen background budgets. -/
theorem Background.connection_third_derivative_budget {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 4 ≤ m) {y : X} (hy : y ∈ Ω) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) y‖ ≤ backgroundThirdConnectionBudget hm K M := by
  exact h.1.connection_third_operator_bound hΩ hK hy
    |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩| |M ⟨4,by omega⟩|
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (fun i j => (h.reference_fderiv_bound (by omega) hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_second_fderiv_bound (by omega) hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_jet_bound ⟨3,by omega⟩ hy i j).trans (le_abs_self _))
    (fun i j => (h.reference_jet_bound ⟨4,by omega⟩ hy i j).trans (le_abs_self _))

end ShrinkingSpheres
