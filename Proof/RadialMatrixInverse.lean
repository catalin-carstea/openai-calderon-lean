import Proof.MetricAlgebra
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
lemma radial_row_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (z : n → ℝ) (hDet : IsUnit G.det)
    (hRad : ∀ j,∑ i,z i*G i j=z j) :
    ∀ j,∑ i,z i*G⁻¹ i j=z j := by
  have hRow : Matrix.vecMul z G=z := funext hRad
  have hh := congrArg (fun w : n → ℝ => Matrix.vecMul w G⁻¹) hRow
  rw [Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv G hDet,Matrix.vecMul_one] at hh
  exact congrFun hh.symm
end ShrinkingSpheres
