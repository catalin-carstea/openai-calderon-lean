module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-! Exact operator identities for the affine term of the moving adjoint.
The normalized conormal and density reciprocal are expanded in the
same operator algebra. -/

public section

set_option autoImplicit false
namespace CalderonN

section
variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem conormal_times_inverseWeight_expansion (B L Q R H₂ : A) (r : ℝ) :
    let S := B+r • (L*B+Q)+r^2 • R
    let H := 1-r • L+r^2 • H₂
    let F := Q-(B*L-L*B)
    let G := B*H₂+(L*B+Q)*(-L+r • H₂)+R*H
    S*H = B+r • F+r^2 • G := by
  dsimp only
  simp only [sub_eq_add_neg,add_mul,mul_add,mul_neg,smul_mul_assoc,mul_smul_comm,mul_one,one_mul,smul_smul]
  module

theorem moving_adjoint_affine_expansion (N B F G M E L R : A) (r b : ℝ)
    (hN : N = B+r • F+r^2 • G) :
    N*(M+b • 1+r^2 • E)-(L+r^2 • R) =
      (B*M-L)+b • B+r • (F*M+b • F)+
        r^2 • (G*(M+b • 1)+N*E-R) := by
  rw [hN]
  simp only [sub_eq_add_neg,add_mul,mul_add,mul_neg,smul_mul_assoc,mul_smul_comm,mul_one,one_mul,smul_smul]
  module

end

end CalderonN
