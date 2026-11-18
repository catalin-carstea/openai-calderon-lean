import Proof.Archive.PolynomialEvaluation
import Proof.Archive.HarmonicRaising
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

noncomputable section
namespace OAI.AnisotropicCalderon.GreenRadialTrace
open MvPolynomial
open OAI.AnisotropicCalderon.AngularPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 
lemma fderiv_eval_coordinate (p : MvPolynomial σ ℝ) (z : σ → ℝ) (i : σ) :
    fderiv ℝ (fun x : σ → ℝ => eval x p) z (Pi.single i 1) =
      eval z (pderiv i p) := by
  classical
  simp [fderiv_eval_apply, Pi.single_apply, ite_mul]

 
def cartesianLaplacian (u : (σ → ℝ) → ℝ) (z : σ → ℝ) : ℝ :=
  ∑ i : σ, fderiv ℝ (fun x => fderiv ℝ u x (Pi.single i 1)) z (Pi.single i 1)

theorem cartesianLaplacian_eval (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    cartesianLaplacian (fun x => eval x p) z = eval z (laplacian p) := by
  classical
  simp only [cartesianLaplacian, fderiv_eval_coordinate, laplacian, map_sum]

 
def driftDerivative (b : σ → ℝ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, C (b i) * pderiv i p

lemma driftDerivative_isHomogeneous {k : ℕ} {p : MvPolynomial σ ℝ}
    (hp : p.IsHomogeneous k) (b : σ → ℝ) :
    (driftDerivative b p).IsHomogeneous (k - 1) := by
  exact IsHomogeneous.sum _ _ _ fun i _ => hp.pderiv.C_mul _

lemma laplacian_driftDerivative (b : σ → ℝ) (p : MvPolynomial σ ℝ)
    (hp : laplacian p = 0) : laplacian (driftDerivative b p) = 0 := by
  simp [driftDerivative, laplacian_sum, laplacian_C_mul, laplacian_pderiv, hp]

 
def driftFirstVariation (k : ℕ) (b : σ → ℝ) (p : MvPolynomial σ ℝ) :=
  radialFirstVariation (k - 1) (driftDerivative b p)

theorem cartesianLaplacian_driftFirstVariation [Nonempty σ] {k : ℕ}
    {p : MvPolynomial σ ℝ} (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0)
    (b z : σ → ℝ) :
    cartesianLaplacian (fun x => eval x (driftFirstVariation k b p)) z =
      -fderiv ℝ (fun x => eval x p) z b := by
  rw [cartesianLaplacian_eval, driftFirstVariation,
    laplacian_radialFirstVariation (driftDerivative_isHomogeneous hp b)
      (laplacian_driftDerivative b p hΔ)
      (ne_of_gt (radiusSq_laplacian_coefficient_pos (k - 1)))]
  simp [driftDerivative, fderiv_eval_apply]

theorem eval_driftFirstVariation_eq_zero (k : ℕ) (b : σ → ℝ)
    (p : MvPolynomial σ ℝ) (z : σ → ℝ) (hz : ∑ i : σ, z i ^ 2 = 1) :
    eval z (driftFirstVariation k b p) = 0 :=
  eval_radialFirstVariation_eq_zero _ _ z hz

 
theorem fderiv_radialFirstVariation_at_sphere (m : ℕ) (q : MvPolynomial σ ℝ)
    (z : σ → ℝ) (hz : ∑ i : σ, z i ^ 2 = 1) :
    fderiv ℝ (fun x => eval x (radialFirstVariation m q)) z z =
      (-2 / (4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ))) * eval z q := by
  have hr : eval z (radiusSq : MvPolynomial σ ℝ) = 1 := by
    simp [radiusSq, hz]
  have hpartial (i : σ) : eval z (pderiv i (radialFirstVariation m q)) =
      -(4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ))⁻¹ * (2 * z i * eval z q) := by
    rw [radialFirstVariation]
    simp only [pderiv_mul, pderiv_C, zero_mul, zero_add, map_sub, pderiv_one,
      sub_zero, pderiv_radiusSq, map_mul, map_add, map_sub, map_ofNat, map_one,
      eval_C, eval_X, hr, sub_self, zero_mul, add_zero]
  rw [fderiv_eval_apply]
  simp_rw [hpartial]
  calc
    _ = (-2 / (4 * (m : ℝ) + 2 * (Fintype.card σ : ℝ))) * eval z q *
        ∑ i : σ, z i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hz, mul_one]

 
theorem fderiv_driftFirstVariation_three_at_sphere {k : ℕ} (hk : 1 ≤ k)
    (b : Fin 3 → ℝ) (p : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ)
    (hz : ∑ i : Fin 3, z i ^ 2 = 1) :
    fderiv ℝ (fun x => eval x (driftFirstVariation k b p)) z z =
      -(2 * (k : ℝ) + 1)⁻¹ * fderiv ℝ (fun x => eval x p) z b := by
  rw [driftFirstVariation, fderiv_radialFirstVariation_at_sphere _ _ z hz]
  have hc : -2 / (4 * ((k - 1 : ℕ) : ℝ) + 2 * (Fintype.card (Fin 3) : ℝ)) =
      -(2 * (k : ℝ) + 1)⁻¹ := by
    rw [Nat.cast_sub hk]
    norm_num only [Fintype.card_fin, Nat.cast_ofNat, Nat.cast_one]
    have hden : 4 * ((k : ℝ) - 1) + 6 = 2 * (2 * (k : ℝ) + 1) := by ring
    rw [hden]
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  rw [hc]
  simp [driftDerivative, fderiv_eval_apply]

lemma driftDerivative_C (b : σ → ℝ) (c : ℝ) : driftDerivative b (C c) = 0 := by
  simp [driftDerivative]

lemma driftFirstVariation_C (k : ℕ) (b : σ → ℝ) (c : ℝ) :
    driftFirstVariation k b (C c) = 0 := by
  simp [driftFirstVariation, driftDerivative_C, radialFirstVariation]

lemma driftDerivative_X (b : σ → ℝ) (j : σ) : driftDerivative b (X j) = C (b j) := by
  classical
  simp [driftDerivative, pderiv_X, Pi.single_apply, mul_ite]

theorem fderiv_driftFirstVariation_three_degree_one (b z : Fin 3 → ℝ)
    (j : Fin 3) (hz : ∑ i : Fin 3, z i ^ 2 = 1) :
    fderiv ℝ (fun x => eval x (driftFirstVariation 1 b (X j))) z z = -(b j) / 3 := by
  rw [fderiv_driftFirstVariation_three_at_sphere (by omega) b (X j) z hz]
  rw [(hasFDerivAt_eval (X j) z).fderiv, polynomialFDeriv_X]
  simp [div_eq_mul_inv]
  ring

end OAI.AnisotropicCalderon.GreenRadialTrace
