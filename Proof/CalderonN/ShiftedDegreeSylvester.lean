module

public import Proof.CalderonN.FiniteSylvesterHalfBound

import Mathlib.Tactic

/-! Generalizes the selected-energy argument from the Proposition 5.3
release f308cb9d to the positive shift (dimension minus two)/2. -/

public section

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SpectralSylvester

lemma shifted_finite_degree_half_form_bound
    {ι : Type*} (s : Finset ι) (degree : ι → ℕ) (K : ι → ι → ℝ)
    (shift M : ℝ) (hShift : (1/2 : ℝ) ≤ shift) (hM : 0 ≤ M)
    (hCasimir : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s,
        ((((degree i:ℝ)+shift)^2-((degree j:ℝ)+shift)^2)*K i j*x j*y i)| ≤
      M*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*x i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*y i^2))
    (u v : ι → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, ((degree i:ℝ)-(degree j:ℝ))*K i j*u j*v i| ≤
      2*M*(1+shift)*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*u i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*v i^2) := by
  let a (i : ι) : ℝ := (degree i:ℝ)+shift
  have ha : ∀ i ∈ s, 0 < a i := by
    intro i _
    dsimp only [a]
    linarith [Nat.cast_nonneg (α := ℝ) (degree i)]
  have hConv (z : ι → ℝ) :
      Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*z i^2) ≤
      2*Real.sqrt (∑ i ∈ s, (a i*z i)^2) := by
    have hEa : 0 ≤ ∑ i ∈ s, (a i*z i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hWeight : (∑ i ∈ s, (1+(degree i:ℝ))^2*z i^2) ≤
        4*(∑ i ∈ s, (a i*z i)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have h₀ : 0 ≤ 1+(degree i:ℝ) := by positivity
      have h₁ : 1+(degree i:ℝ) ≤ 2*a i := by
        dsimp only [a]
        linarith [Nat.cast_nonneg (α := ℝ) (degree i)]
      calc
        _ ≤ (2*a i)^2*z i^2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h₀ h₁ 2) (sq_nonneg _)
        _ = _ := by ring
    have hSquare : (2*Real.sqrt (∑ i ∈ s, (a i*z i)^2))^2 =
        4*(∑ i ∈ s, (a i*z i)^2) := by
      rw [mul_pow, Real.sq_sqrt hEa]
      ring
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hWeight.trans_eq hSquare.symm⟩
  have hD : ∀ x y : ι → ℝ,
      |∑ i ∈ s, ∑ j ∈ s, (a i^2-a j^2)*K i j*x j*y i| ≤
        ((4*M)/2)*((∑ i ∈ s, (a i*x i)^2)+(∑ i ∈ s, (a i*y i)^2)) := by
    intro x y
    let X : ℝ := ∑ i ∈ s, (a i*x i)^2
    let Y : ℝ := ∑ i ∈ s, (a i*y i)^2
    have hX : 0 ≤ X := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hY : 0 ≤ Y := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hProd : Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*x i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*y i^2) ≤
        (2*Real.sqrt X)*(2*Real.sqrt Y) :=
      mul_le_mul (hConv x) (hConv y) (Real.sqrt_nonneg _) (by positivity)
    have hYoung : 2*Real.sqrt X*Real.sqrt Y ≤ X+Y := by
      have hXsq := Real.sq_sqrt hX
      have hYsq := Real.sq_sqrt hY
      nlinarith [sq_nonneg (Real.sqrt X-Real.sqrt Y)]
    calc
      _ ≤ M*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*x i^2)*
          Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*y i^2) :=
        hCasimir x y
      _ = M*(Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*x i^2)*
          Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))^2*y i^2)) := by ring
      _ ≤ M*((2*Real.sqrt X)*(2*Real.sqrt Y)) := mul_le_mul_of_nonneg_left hProd hM
      _ = (2*M)*(2*Real.sqrt X*Real.sqrt Y) := by ring
      _ ≤ (2*M)*(X+Y) := mul_le_mul_of_nonneg_left hYoung (by positivity)
      _ = _ := by ring
  have hHalf := finite_sylvester_half_form_bound s a ha K (4*M) (by positivity) hD u v
  have hDegree : (∑ i ∈ s, ∑ j ∈ s, (a i-a j)*K i j*u j*v i) =
      ∑ i ∈ s, ∑ j ∈ s, ((degree i:ℝ)-(degree j:ℝ))*K i j*u j*v i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [a]
    ring
  have hShift₀ : 0 ≤ shift := by linarith
  have hScale : 0 ≤ 1+shift := by positivity
  have hPhysical (z : ι → ℝ) :
      Real.sqrt (∑ i ∈ s, a i*z i^2) ≤
      Real.sqrt (1+shift)*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*z i^2) := by
    rw [← Real.sqrt_mul hScale]
    apply Real.sqrt_le_sqrt
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    dsimp only [a]
    nlinarith [mul_nonneg hShift₀ (Nat.cast_nonneg (α := ℝ) (degree i))]
  have hProd := mul_le_mul (hPhysical u) (hPhysical v)
    (Real.sqrt_nonneg _) (by positivity)
  calc
    _ ≤ ((4*M)/2)*Real.sqrt (∑ i ∈ s, a i*u i^2)*Real.sqrt (∑ i ∈ s, a i*v i^2) :=
      (congrArg abs hDegree).symm.trans_le hHalf
    _ ≤ ((4*M)/2)*((Real.sqrt (1+shift)*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*u i^2))*
        (Real.sqrt (1+shift)*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*v i^2))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hProd (by positivity)
    _ = _ := by
      have hh := Real.sq_sqrt hScale
      linear_combination (2*M*Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*u i^2)*
        Real.sqrt (∑ i ∈ s, (1+(degree i:ℝ))*v i^2))*hh

end OAI.AnisotropicCalderon.SpectralSylvester
