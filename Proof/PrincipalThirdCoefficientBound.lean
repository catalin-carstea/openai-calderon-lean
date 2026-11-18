import Proof.CoordinateThirdJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def principalThirdEntryBudget (K M1 M2 M3 : ℝ) : ℝ :=
  9*(K^2*M3+4*K*(9*K^2*M1)*M2+
    (2*K*(9*(162*K^3*M1^2+9*K^2*M2))+2*(9*K^2*M1)^2)*M1)

lemma principalThirdEntryBudget_nonneg (K M1 M2 M3 : ℝ)
    (hK : 0 ≤ K) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) :
    0 ≤ principalThirdEntryBudget K M1 M2 M3 := by
  unfold principalThirdEntryBudget
  positivity

/-- Third principal coordinate jets follow from the actual inverse metric
and the original eight-jet perturbation budget, for arbitrary profiles. -/
theorem principal_third_le_inverse_add {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K) {r : X → ℝ} {ε : ℝ}
    (hs : Small Y g g₂ r ε) {y : X} (hy : y ∈ Y)
    (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M1)
    (hD2 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M2)
    (hD3 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => g x a b))) y‖ ≤ M3)
    (a b i j k : I) :
    |coordDeriv i (coordDeriv j (coordDeriv k (fun x => principal g g₂ x a b))) y| ≤
      principalThirdEntryBudget K M1 M2 M3+ε*r y := by
  have hQ := contDiffOn_principal_entry h h₂ hK a b
  have hInv := h.contDiffOn_inverse_entry hK a b
  have hEq : coordDeriv i (coordDeriv j (coordDeriv k (fun x => (principal g g₂ x-(g x)⁻¹) a b))) y =
      coordDeriv i (coordDeriv j (coordDeriv k (fun x => principal g g₂ x a b))) y-
        coordDeriv i (coordDeriv j (coordDeriv k (fun x => (g x)⁻¹ a b))) y := by
    simpa only [Matrix.sub_apply] using coordinate_third_sub hY hQ hInv hy i j k
  have hSmall := hs.coordinate_third_component_bound hY h h₂ hK hy i j k a b
  have hSub := (congrArg abs hEq).symm.le.trans hSmall
  have hInvNorm := h.inverse_third_fderiv_bound hY hK hy M1 M2 M3 hM1 hM2 hM3 hD hD2 hD3 a b
  have hInvC : |coordDeriv i (coordDeriv j (coordDeriv k (fun x => (g x)⁻¹ a b))) y| ≤
      principalThirdEntryBudget K M1 M2 M3 :=
    (coordinate_third_abs_le_iterated hY hInv hy i j k).trans (by
      simpa only [norm_iteratedFDeriv_three_eq_nested,principalThirdEntryBudget] using hInvNorm)
  calc
    _ = |coordDeriv i (coordDeriv j (coordDeriv k (fun x => (g x)⁻¹ a b))) y+
        (coordDeriv i (coordDeriv j (coordDeriv k (fun x => principal g g₂ x a b))) y-
          coordDeriv i (coordDeriv j (coordDeriv k (fun x => (g x)⁻¹ a b))) y)| := by congr 1;ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hInvC hSub)

end ShrinkingSpheres
