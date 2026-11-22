module

public import Proof.CalderonN.Coordinates
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

@[expose] public section

noncomputable section
open Matrix MvPolynomial

namespace CalderonPatch

open CalderonN (I Mat)

variable {n : ℕ}

/-- The degree-two symbol of a scalar elliptic operator at a point. -/
def ellipticQuadraticSymbol (A : Mat n) : MvPolynomial (I n) ℝ :=
  ∑ i : I n, ∑ j : I n, C (A i j) * X i * X j

theorem ellipticQuadraticSymbol_homogeneous (A : Mat n) :
    MvPolynomial.IsHomogeneous (ellipticQuadraticSymbol A) 2 := by
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  exact ((isHomogeneous_C _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X _ _)

theorem ellipticQuadraticSymbol_ne_zero [NeZero n] {A : Mat n} (hA : Matrix.PosDef A) :
    ellipticQuadraticSymbol A ≠ 0 := by
  let i : I n := 0
  have he : MvPolynomial.eval (Pi.single i (1 : ℝ)) (ellipticQuadraticSymbol A) = A i i := by
    simp [ellipticQuadraticSymbol, Pi.single_apply, mul_ite]
  intro h
  rw [h, map_zero] at he
  exact (hA.diag_pos (i := i)).ne' he.symm

/-- The principal homogeneous term in the image of a point-supported
distribution is the product of its principal polynomial and the
nonzero elliptic quadratic symbol. Terms of lower order cannot cancel it. -/
theorem pointDistribution_symbol_order [NeZero n]
    {A : Mat n} (hA : Matrix.PosDef A) {P R : MvPolynomial (I n) ℝ} (hP : P ≠ 0)
    (hR : R.totalDegree < P.totalDegree + 2) :
    (P * ellipticQuadraticSymbol A + R).totalDegree = P.totalDegree + 2 := by
  have hQ := ellipticQuadraticSymbol_ne_zero hA
  have hTop : (P * ellipticQuadraticSymbol A).totalDegree = P.totalDegree + 2 := by
    rw [totalDegree_mul_of_isDomain hP hQ, (ellipticQuadraticSymbol_homogeneous A).totalDegree hQ]
  rw [totalDegree_add_eq_left_of_totalDegree_lt (hTop.symm ▸ hR), hTop]

/-- An image of order at most two forces the polynomial of a nonzero
point-supported preimage to be constant. -/
theorem pointDistribution_symbol_constant_of_image_order_le_two [NeZero n]
    {A : Mat n} (hA : Matrix.PosDef A) {P R : MvPolynomial (I n) ℝ} (hP : P ≠ 0)
    (hR : R.totalDegree < P.totalDegree + 2) (hOrder : (P * ellipticQuadraticSymbol A + R).totalDegree ≤ 2) :
    ∃ c : ℝ, P = C c := by
  have h := pointDistribution_symbol_order hA hP hR
  have hzero : P.totalDegree = 0 := by omega
  exact ⟨P.coeff 0, totalDegree_eq_zero_iff_eq_C.mp hzero⟩

end CalderonPatch
