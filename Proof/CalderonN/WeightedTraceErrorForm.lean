module

public import Proof.CalderonN.SmoothTraceAngularOrder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Tactic

/-! The form estimate after the one base integration by parts in
Proposition 5.3. The three coefficient orders use precisely the two
higher angular terms of the energy. -/

public section

noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4200000
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem weighted_trace_cross_le {β H V : ℝ} (hβ : 0 < β) :
    H*V ≤ (β⁻¹*H^2 + β*V^2)/2 := by
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).2
  apply (mul_le_mul_iff_of_pos_left hβ).mp
  calc
    _ ≤ H^2+(β*V)^2 := by nlinarith only [sq_nonneg (H-β*V)]
    _ = _ := by rw [mul_add,← mul_assoc, mul_inv_cancel₀ hβ.ne',one_mul]; ring

theorem abs_weighted_trace_error_density_le (hn : 3 ≤ dim)
    (φ : SmoothSphereTrace dim) (H : I dim → SmoothSphereTrace dim)
    (E₂ : I dim → I dim → Module.End ℝ (SmoothSphereTrace dim))
    (E₁ : I dim → Module.End ℝ (SmoothSphereTrace dim))
    (E₀ : Module.End ℝ (SmoothSphereTrace dim))
    (β C : ℝ) (hβ : 0 < β) (hC : 0 ≤ C)
    (h₂ : ∀ i j, SmoothTraceAngularBound hn 1 (C*β⁻¹) (E₂ i j))
    (h₁ : ∀ i, SmoothTraceAngularBound hn 2 C (E₁ i))
    (h₀ : SmoothTraceAngularBound hn 3 (C*β) E₀) :
    let L := smoothSphereTraceL2 hn
    let h := traceOrderNorm hn 2
    let v := traceOrderNorm hn 3 φ
    |(∑ i,∑ j, ⟪L (E₂ i j (H j)), L (H i)⟫_ℝ)+
       (∑ i, ⟪L (E₁ i (H i)), L φ⟫_ℝ)+⟪L (E₀ φ),L φ⟫_ℝ| ≤
      ((dim:ℝ)^2+dim+1)*C*(β⁻¹*(∑ i,h (H i)^2)+β*v^2) := by
  dsimp only
  let L := smoothSphereTraceL2 (dim:=dim) hn
  let h (i : I dim) := traceOrderNorm hn 2 (H i)
  let v := traceOrderNorm hn 3 φ
  let N := β⁻¹*(∑ i,h i^2)+β*v^2
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hHi (i : I dim) : β⁻¹*h i^2 ≤ N := by
    have hh : h i^2 ≤ ∑ j,h j^2 := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hβ.le)).trans (le_add_of_nonneg_right (by positivity))
  have hV : β*v^2 ≤ N := le_add_of_nonneg_left (by positivity)
  have hQ₂ (i j : I dim) : |⟪L (E₂ i j (H j)),L (H i)⟫_ℝ| ≤ C*N := by
    have hP : |⟪L (E₂ i j (H j)),L (H i)⟫_ℝ| ≤ C*β⁻¹*h j*h i :=
      (h₂ i j).abs_pair_le 1 2 (by decide) (H j) (H i)
    have hYoung : h j*h i ≤ (h i^2+h j^2)/2 := by nlinarith only [sq_nonneg (h j-h i)]
    refine hP.trans ?_
    have h := mul_le_mul_of_nonneg_left hYoung (mul_nonneg hC (inv_nonneg.mpr hβ.le))
    have h' := add_le_add (hHi i) (hHi j)
    have h'' := mul_le_mul_of_nonneg_left h' (show 0 ≤ C/2 by positivity)
    nlinarith only [h,h'']
  have hQ₁ (i : I dim) : |⟪L (E₁ i (H i)),L φ⟫_ℝ| ≤ C*N := by
    have hP : |⟪L (E₁ i (H i)),L φ⟫_ℝ| ≤ C*h i*v :=
      (h₁ i).abs_pair_le 0 2 (by decide) (H i) φ
    refine hP.trans ?_
    have hCross := weighted_trace_cross_le (H:=h i) (V:=v) hβ
    have hM := mul_le_mul_of_nonneg_left hCross hC
    have h' := mul_le_mul_of_nonneg_left (add_le_add (hHi i) hV) (show 0 ≤ C/2 by positivity)
    nlinarith only [hM,h']
  have hQ₀ : |⟪L (E₀ φ),L φ⟫_ℝ| ≤ C*N := by
    have hP : |⟪L (E₀ φ),L φ⟫_ℝ| ≤ C*β*v*v :=
      h₀.abs_pair_le 0 3 (by decide) φ φ
    exact hP.trans ((by ring : C*β*v*v = C*(β*v^2)) ▸ mul_le_mul_of_nonneg_left hV hC)
  have h₂' : |∑ i,∑ j,⟪L (E₂ i j (H j)),L (H i)⟫_ℝ| ≤ (dim:ℝ)^2*(C*N) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => hQ₂ i j)).trans_eq ?_
    simp [pow_two,mul_assoc]
  have h₁' : |∑ i,⟪L (E₁ i (H i)),L φ⟫_ℝ| ≤ (dim:ℝ)*(C*N) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun i _ => hQ₁ i).trans_eq (by simp))
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₂' h₁')) hQ₀)).trans_eq (by
    change (dim:ℝ)^2*(C*N)+dim*(C*N)+C*N = ((dim:ℝ)^2+dim+1)*C*N
    ring)

/-- Integration uses the same weight and the same half-order horizontal
and mass norms as the local form. -/
theorem abs_integral_weighted_trace_error_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {q energy : X → ℝ} (hq : Integrable q μ) (hE : Integrable energy μ)
    {C : ℝ} (hBound : ∀ᵐ x ∂μ, |q x| ≤ C*energy x) :
    |∫ x,q x ∂μ| ≤ C*∫ x,energy x ∂μ := by
  rw [← integral_const_mul]
  refine abs_integral_le_integral_abs.trans ?_
  exact integral_mono_ae hq.abs (hE.const_mul C) hBound

end CalderonN
