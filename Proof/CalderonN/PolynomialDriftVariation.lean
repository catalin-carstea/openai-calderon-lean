module

public import Proof.CalderonN.EuclideanPolynomialEvaluation
public import Proof.CalderonN.BoundedHarmonicShift
public import Proof.CalderonN.HarmonicMultiplier
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

public section

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

 
@[expose] def driftDerivative (b : σ → ℝ) (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, C (b i) * pderiv i p

lemma driftDerivative_isHomogeneous {k : ℕ} {p : MvPolynomial σ ℝ}
    (hp : p.IsHomogeneous k) (b : σ → ℝ) :
    (driftDerivative b p).IsHomogeneous (k - 1) := by
  exact IsHomogeneous.sum _ _ _ fun i _ => hp.pderiv.C_mul _

lemma laplacian_driftDerivative (b : σ → ℝ) (p : MvPolynomial σ ℝ)
    (hp : laplacian p = 0) : laplacian (driftDerivative b p) = 0 := by
  simp [driftDerivative, laplacian_sum, laplacian_C_mul, laplacian_pderiv, hp]

 
@[expose] def driftFirstVariation (k : ℕ) (b : σ → ℝ) (p : MvPolynomial σ ℝ) :=
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

 
/-- The first normalized radial derivative contributes one degree of lowering
    and the coefficient (2m+n)⁻¹ when the output has degree m. -/
theorem fderiv_driftFirstVariation_at_sphere {n : ℕ}
    (m : ℕ) (b z : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ)
    (hz : ∑ i : Fin n, z i ^ 2 = 1) :
    fderiv ℝ (fun x => eval x (driftFirstVariation (m+1) b p)) z z =
      -(2 * (m : ℝ) + (n : ℝ))⁻¹ * fderiv ℝ (fun x => eval x p) z b := by
  rw [driftFirstVariation, Nat.add_sub_cancel, fderiv_radialFirstVariation_at_sphere _ _ z hz]
  have hc : -2 / (4 * (m : ℝ) + 2 * (Fintype.card (Fin n) : ℝ)) =
      -(2 * (m : ℝ) + (n : ℝ))⁻¹ := by
    rw [Fintype.card_fin, show 4 * (m : ℝ) + 2 * (n : ℝ) = 2*(2*(m : ℝ)+(n : ℝ)) by ring]
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

theorem euclidean_radial_driftFirstVariation {n : ℕ} (m : ℕ)
    (b z : CalderonN.X n) (p : MvPolynomial (Fin n) ℝ) (hz : ‖z‖ = 1) :
    fderiv ℝ (polynomialEvaluation (driftFirstVariation (m+1) (fun i => b i) p)) z z =
      -(2 * (m : ℝ) + (n : ℝ))⁻¹ * fderiv ℝ (polynomialEvaluation p) z b := by
  have hs : ∑ i : Fin n, z i ^ 2 = 1 := by
    simpa only [hz,one_pow] using (EuclideanSpace.real_norm_sq_eq z).symm
  rw [fderiv_polynomialEvaluation_eq_coordinate, fderiv_polynomialEvaluation_eq_coordinate]
  exact fderiv_driftFirstVariation_at_sphere m _ _ p hs

end OAI.AnisotropicCalderon.GreenRadialTrace

namespace CalderonN

open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

private def radialDriftWeight (n m : ℕ) : ℝ :=
  -((m : ℝ)+2)/(2*(m : ℝ)+(n : ℝ))

private theorem abs_radialDriftWeight_le (m : ℕ) : |radialDriftWeight n m| ≤ 2 := by
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hDen : 0 < 2*(m : ℝ)+(n : ℝ) := by linarith
  rw [radialDriftWeight, abs_div, abs_neg, abs_of_nonneg (by positivity), abs_of_pos hDen]
  exact (div_le_iff₀ hDen).2 (by linarith)

/-- The zeroth-order radial Dirichlet variation on the actual Hilbert sphere.
    Its coefficient is the directional first variation of the normalized scalar density. -/
def radialDriftOperator (b : X n) : SphereL2 n →L[ℝ] SphereL2 n :=
  (harmonicMultiplier (radialDriftWeight n) 2 zero_le_two abs_radialDriftWeight_le).comp
    (∑ i, b i • normalizedLowering i)

theorem radialDriftOperator_projection (b : X n) (u : SphereL2 n) (m : ℕ) :
    harmonicProjection m (radialDriftOperator b u) =
      ∑ i, (-(2*(m : ℝ)+(n : ℝ))⁻¹ * b i) •
        harmonicDerivative (sphereFischerInner n) m i (harmonicProjection (m+1) u) := by
  simp only [radialDriftOperator, ContinuousLinearMap.comp_apply, harmonicProjection_harmonicMultiplier,
    ContinuousLinearMap.sum_apply, smul_apply, map_sum, map_smul, normalizedLowering_projection,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have hm : (0 : ℝ) < (m : ℝ)+2 := by positivity
  unfold radialDriftWeight
  field_simp [hm.ne']

end CalderonN
