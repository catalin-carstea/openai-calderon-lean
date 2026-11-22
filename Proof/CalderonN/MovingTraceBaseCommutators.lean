module

public import Mathlib.Algebra.Ring.Basic

import Mathlib.Tactic

/-! Base derivatives of coefficient families are commutators with the
coordinate derivative. A scalar principal coefficient removes the third
base derivative in the moving trace comparison. -/

public section

set_option autoImplicit false
namespace CalderonN

section
variable {R : Type*} [Ring R]

theorem commutator_base_one_one (P Q D E : R) (hDE : D*E = E*D) :
    (P*D)*(Q*E)-(Q*E)*(P*D) =
      (P*Q-Q*P)*D*E + P*(D*Q-Q*D)*E - Q*(E*P-P*E)*D := by
  noncomm_ring [hDE]

theorem commutator_base_zero_one (P Q D : R) :
    P*(Q*D)-(Q*D)*P = (P*Q-Q*P)*D-Q*(D*P-P*D) := by
  noncomm_ring

theorem commutator_base_zero_two (P a D E : R) (hPa : P*a = a*P) :
    P*(a*D*E)-(a*D*E)*P =
      -a*(D*P-P*D)*E-a*(E*P-P*E)*D-
        a*(D*(E*P-P*E)-(E*P-P*E)*D) := by
  have hPa' : P*(a*(D*E)) = a*(P*(D*E)) := by rw [← mul_assoc, hPa, mul_assoc]
  noncomm_ring [hPa,hPa']

theorem commutator_base_one_two (P a D E F : R)
    (hPa : P*a = a*P) (hDE : D*E = E*D) (hDF : D*F = F*D) :
    (P*D)*(a*E*F)-(a*E*F)*(P*D) =
      P*(D*a-a*D)*E*F - a*(E*P-P*E)*F*D - a*(F*P-P*F)*E*D-
        a*(E*(F*P-P*F)-(F*P-P*F)*E)*D := by
  have hDF' : E*(D*F) = E*(F*D) := congrArg (E * ·) hDF
  have hPa' : P*(a*(E*(F*D))) = a*(P*(E*(F*D))) := by rw [← mul_assoc,hPa,mul_assoc]
  noncomm_ring [hPa,hDE,hDF,hDF',hPa']

theorem commutator_of_same_base_principal_part (B P Q : R) :
    (B+P)*(B+Q)-(B+Q)*(B+P) =
      (P-Q)*(B+Q)-(B+Q)*(P-Q) := by
  noncomm_ring

end

end CalderonN
