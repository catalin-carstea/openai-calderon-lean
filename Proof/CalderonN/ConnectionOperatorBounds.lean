module

public import Proof.CalderonN.ChristoffelDerivative
public import Proof.CalderonN.CurvatureSkew

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 10
open Set
open scoped ContDiff
namespace CalderonN
variable {n : ℕ}

lemma norm_euclidean_proj_le_one (i : (I n)) : ‖(EuclideanSpace.proj i : (X n) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [PiLp.proj_apply, one_mul] using PiLp.norm_apply_le v i

def coordinateBilinearAtom (i j k : (I n)) : (X n) →L[ℝ] (X n) →L[ℝ] (X n) :=
  (EuclideanSpace.proj i).smulRight ((EuclideanSpace.proj j).smulRight (axis k))

lemma coordinateBilinearAtom_norm_le_one (i j k : (I n)) : ‖coordinateBilinearAtom i j k‖ ≤ 1 := by
  rw [coordinateBilinearAtom, ContinuousLinearMap.norm_smulRight_apply,
    ContinuousLinearMap.norm_smulRight_apply, norm_axis, mul_one]
  exact (mul_le_mul (norm_euclidean_proj_le_one i) (norm_euclidean_proj_le_one j)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

lemma norm_coordinateBilinear_sum_le (c : (I n) → (I n) → (I n) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ i j k, |c i j k| ≤ C) :
    ‖∑ i, ∑ j, ∑ k, c i j k • coordinateBilinearAtom i j k‖ ≤ (n:ℝ)^3*C := by
  have hterm (i j k : (I n)) : ‖c i j k • coordinateBilinearAtom i j k‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |c i j k| * 1 := mul_le_mul_of_nonneg_left (coordinateBilinearAtom_norm_le_one i j k) (abs_nonneg _)
      _ ≤ C := by simpa only [mul_one] using hc i j k
  calc
    _ ≤ ∑ i, ‖∑ j, ∑ k, c i j k • coordinateBilinearAtom i j k‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖∑ k, c i j k • coordinateBilinearAtom i j k‖ := Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ∑ k, ‖c i j k • coordinateBilinearAtom i j k‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => norm_sum_le _ _))
    _ ≤ ∑ _i : (I n), ∑ _j : (I n), ∑ _k : (I n), C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hterm i j k)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma connectionBilinear_norm_of_entry_bound (g : (MetricField n)) (y : (X n)) (C : ℝ) (hC : 0 ≤ C)
    (hΓ : ∀ k i j, |christoffel g y k i j| ≤ C) : ‖connectionBilinear g y‖ ≤ (n:ℝ)^3*C :=
  norm_coordinateBilinear_sum_le (fun i j k => christoffel g y k i j) C hC (fun i j k => hΓ k i j)

lemma fderiv_connectionBilinear_apply {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (a : (X n)) :
    fderiv ℝ (connectionBilinear g) y a =
      ∑ i, ∑ j, ∑ k, fderiv ℝ (fun x => christoffel g x k i j) y a • coordinateBilinearAtom i j k := by
  have hΓ (i j k : (I n)) := (((h.contDiffOn_christoffel hΩ hK k i j).contDiffAt
    (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.smul_const (coordinateBilinearAtom i j k)
  have hsum := HasFDerivAt.sum (u:=Finset.univ) (fun i _ =>
    HasFDerivAt.sum (u:=Finset.univ) (fun j _ =>
      HasFDerivAt.sum (u:=Finset.univ) (fun k _ => hΓ i j k)))
  have hfun : connectionBilinear g =
      ∑ i, ∑ j, ∑ k, (fun x => christoffel g x k i j • coordinateBilinearAtom i j k) := by
    funext x
    simp only [connectionBilinear, coordinateBilinearAtom, Finset.sum_apply]
  rw [hfun, hsum.fderiv]
  simp only [_root_.sum_apply, ContinuousLinearMap.smulRight_apply]

lemma fderiv_connectionBilinear_norm_of_entry_bound {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω) (D : ℝ) (hD : 0 ≤ D)
    (hΓ : ∀ a k i j, |fderiv ℝ (fun x => christoffel g x k i j) y a| ≤ D*‖a‖) :
    ‖fderiv ℝ (connectionBilinear g) y‖ ≤ (n:ℝ)^3*D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  rw [fderiv_connectionBilinear_apply hΩ h hK hy a]
  exact (norm_coordinateBilinear_sum_le _ (D*‖a‖) (by positivity)
    (fun i j k => hΓ a k i j)).trans_eq (by ring)

/-- Connection operator bounds depend only on ellipticity and the first two metric budgets. -/
theorem Elliptic.connection_operator_bounds {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : (X n)} (hy : y ∈ Ω)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ i j, ‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (hD₂ : ∀ i j, ‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂) :
    ‖connectionBilinear g y‖ ≤ (n:ℝ)^3*(3*(n:ℝ)*K*M₁) ∧
      ‖fderiv ℝ (connectionBilinear g) y‖ ≤ (n:ℝ)^3*(3*(n:ℝ)^3*K^2*M₁^2+3*(n:ℝ)*K*M₂) := by
  exact ⟨connectionBilinear_norm_of_entry_bound g y _ (by positivity)
      (fun k i j => h.christoffel_entry_bound hK hy M₁ hM₁ hD k i j),
    fderiv_connectionBilinear_norm_of_entry_bound hΩ h hK hy _ (by positivity)
      (fun a k i j => h.christoffel_derivative_entry_bound hΩ hK hy M₁ M₂ hM₁ hM₂ hD hD₂ a k i j)⟩

end CalderonN
