module

public import Proof.CalderonN.MovingTraceBaseCommutators

import Mathlib.Tactic

/-! Coordinate formal-adjoint algebra for the base derivatives with
respect to a density. The logarithmic density derivatives act on the left. -/

public section

set_option autoImplicit false
namespace CalderonN

section
variable {R : Type*} [Ring R]

theorem adjoint_base_one_normal (Bstar D μ : R) :
    -(D+μ)*Bstar = -(Bstar*D)-(D*Bstar-Bstar*D+μ*Bstar) := by
  noncomm_ring

theorem adjoint_base_two_normal (a D E μ ν : R) (hED : E*D = D*E) :
    let p := D*a-a*D+μ*a
    let q := E*a-a*E+ν*a
    (E+ν)*(D+μ)*a = a*D*E+p*E+q*D+(E*p-p*E)+ν*p := by
  dsimp only
  have hEDa : E*(D*a) = D*(E*a) := by rw [← mul_assoc,hED,mul_assoc]
  noncomm_ring [hED,hEDa]

/-- With the scalar second-derivative coefficient self-adjoint, the
adjoint difference has one base derivative at most. -/
theorem movingTrace_adjoint_difference_monomial
    (a B C Bstar Cstar D E μ ν : R) (hED : E*D = D*E) :
    let p := D*a-a*D+μ*a
    let q := E*a-a*E+ν*a
    ((E+ν)*(D+μ)*a-(D+μ)*Bstar+Cstar)-(a*D*E+B*D+C) =
      p*E+(q-Bstar-B)*D+
      ((E*p-p*E)+ν*p-(D*Bstar-Bstar*D+μ*Bstar)+Cstar-C) := by
  dsimp only
  rw [adjoint_base_two_normal a D E μ ν hED]
  noncomm_ring

end

end CalderonN
