module

public import Proof.CalderonN.HarmonicDerivativeOperator
public import Proof.CalderonN.FiniteDriftRadialOperator
public import Proof.CalderonN.EuclideanPolynomialEvaluation

import Mathlib.Tactic

/-! The coordinate decomposition and double-raising cancellation from
the Proposition 5.3 release hold with the dimension-dependent shift. -/

public section

noncomputable section
open MvPolynomial
open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace

variable {dim : ℕ} [NeZero dim]

@[expose] def coordinateHarmonicRaising (k : ℕ) (i : Fin dim)
    (p : MvPolynomial (Fin dim) ℝ) : MvPolynomial (Fin dim) ℝ :=
  MvPolynomial.X i*p-C ((2*(k:ℝ)+(dim:ℝ)-2)⁻¹)*radiusSq*pderiv i p

theorem sphereDerivativeAdjoint_eq_coordinateRaising (k : ℕ) (i : Fin dim)
    (p : MvPolynomial (Fin dim) ℝ) (hp : p ∈ harmonicHomogeneous dim k) :
    sphereDerivativeAdjoint k i p =
      C ((dim:ℝ)+2*(k:ℝ))*coordinateHarmonicRaising k i p := by
  cases k with
  | zero =>
    rw [eq_C_of_mem_harmonicHomogeneous_zero hp]
    simp [sphereDerivativeAdjoint,coordinateHarmonicRaising]
  | succ m =>
    have hR : polynomialRaising (Pi.single i p) = MvPolynomial.X i*p := by
      classical
      simp [polynomialRaising,Pi.single_apply,mul_ite]
    have hD : polynomialDivergence (Pi.single i p) = pderiv i p := by
      classical
      simp [polynomialDivergence,Pi.single_apply,apply_ite]
    have hPos : 0 < (dim:ℝ) := by exact_mod_cast NeZero.pos dim
    have hDen : (4*(m:ℝ)+2*(dim:ℝ)) = 2*(2*(m:ℝ)+(dim:ℝ)) := by ring
    have hCoef : 2/(4*(m:ℝ)+2*(dim:ℝ)) = (2*((m+1:ℕ):ℝ)+(dim:ℝ)-2)⁻¹ := by
      rw [hDen,div_mul_eq_div_div]
      push_cast
      rw [show 2*((m:ℝ)+1)+(dim:ℝ)-2 = 2*(m:ℝ)+(dim:ℝ) by ring]
      norm_num [one_div]
    simp only [sphereDerivativeAdjoint,polynomialSphereRaising,harmonicRaising,hR,hD,
      Fintype.card_fin,hCoef,coordinateHarmonicRaising,Nat.cast_add,Nat.cast_one]

theorem coordinateHarmonicRaising_mem (k : ℕ) (i : Fin dim)
    (p : MvPolynomial (Fin dim) ℝ) (hp : p ∈ harmonicHomogeneous dim k) :
    coordinateHarmonicRaising k i p ∈ harmonicHomogeneous dim (k+1) := by
  have hPos : 0 < (dim:ℝ)+2*(k:ℝ) := by
    have : 0 < (dim:ℝ) := by exact_mod_cast NeZero.pos dim
    positivity
  have h := (harmonicHomogeneous dim (k+1)).smul_mem ((dim:ℝ)+2*(k:ℝ))⁻¹
    (sphereDerivativeAdjoint_harmonicHomogeneous k i p hp)
  rwa [sphereDerivativeAdjoint_eq_coordinateRaising k i p hp,← smul_eq_C_mul,smul_smul,
    inv_mul_cancel₀ hPos.ne',one_smul] at h

theorem polynomialEvaluation_mul_coordinate_split (k : ℕ) (i : Fin dim)
    (p : MvPolynomial (Fin dim) ℝ) (z : X dim) (hz : z ∈ standardSphere dim) :
    z i*polynomialEvaluation p z =
      polynomialEvaluation (coordinateHarmonicRaising k i p) z+
        (2*(k:ℝ)+(dim:ℝ)-2)⁻¹*polynomialEvaluation (pderiv i p) z := by
  have hr : polynomialEvaluation (radiusSq : MvPolynomial (Fin dim) ℝ) z = 1 := by
    simp only [polynomialEvaluation,radiusSq,map_sum,map_pow,eval_X]
    exact unitSphere_sum_sq ⟨z,hz⟩
  unfold coordinateHarmonicRaising
  have h : polynomialEvaluation (MvPolynomial.X i) z = z i := by
    simp [polynomialEvaluation,eval_X]
    rfl
  change z i*polynomialEvaluation p z = eval (euclideanCoordinates dim z) _+_
  simp only [map_sub,map_mul,eval_C,show eval (euclideanCoordinates dim z) (MvPolynomial.X i) = z i from h,
    show eval (euclideanCoordinates dim z) radiusSq = 1 from hr,mul_one]
  change _ = z i*polynomialEvaluation p z-
    (2*(k:ℝ)+(dim:ℝ)-2)⁻¹*polynomialEvaluation (pderiv i p) z+
    (2*(k:ℝ)+(dim:ℝ)-2)⁻¹*polynomialEvaluation (pderiv i p) z
  ring

theorem sum_double_harmonicDerivativeAdjoint_eq_zero (k : ℕ) (u : harmonicSphereSubspace dim k) :
    (∑ i : Fin dim, harmonicDerivativeAdjoint (sphereFischerInner dim) (k+1) i
      (harmonicDerivativeAdjoint (sphereFischerInner dim) k i u)) = 0 := by
  apply ext_inner_right ℝ
  intro v
  rcases harmonicPolynomialSphereMap_surjective (k+2) v with ⟨p,rfl⟩
  simp only [sum_inner,inner_zero_left,inner_harmonicDerivativeAdjoint,harmonicDerivative_apply_image]
  have hsum : (∑ i : Fin dim,
      harmonicDerivative (sphereFischerInner dim) k i
        (harmonicPolynomialDerivativeMap (k+1) i p)) = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_zero]
    have h (i : Fin dim) :
        ((harmonicDerivative (sphereFischerInner dim) k i
            (harmonicPolynomialDerivativeMap (k+1) i p) : harmonicSphereSubspace dim k) :
            SphereL2 dim) = polynomialSphereL2 (pderiv i (pderiv i p.1)) := by
      change ((harmonicDerivative (sphereFischerInner dim) k i
        (harmonicPolynomialSphereMap (k+1) ⟨pderiv i p.1,
          pderiv_harmonicHomogeneous_succ (k+1) i p.1 p.2⟩) : harmonicSphereSubspace dim k) :
          SphereL2 dim) = _
      rw [harmonicDerivative_apply_image]
      rfl
    simp only [h,← map_sum]
    change polynomialSphereL2 (laplacian p.1) = 0
    rw [p.2.2,map_zero]
  rw [← inner_sum,hsum,inner_zero_right]

end CalderonN
