module

public import Proof.CalderonN.MovingTraceDivergenceForm

import Mathlib.Tactic

/-! The first-order and multiplication pieces of the integrated
commutators in coordinate base derivatives. -/

public section

set_option autoImplicit false
namespace CalderonN

section Algebra
variable {R : Type*} [Ring R]

theorem normalToDivergence_base_two (a D Dd E μ : R) (hD : Dd = -D-μ) :
    a*D*E = Dd*(-a)*E-(D*a-a*D+μ*a)*E := by
  rw [hD]
  noncomm_ring

theorem pairedAdjoint_difference_divergence_first (b b' c c' D Dd μ : R) (hD : Dd = -D-μ) :
    (Dd*b'+c')-(b*D+c) =
      (-b'-b)*D+(c'-c-(D*b'-b'*D)-μ*b') := by
  rw [hD]
  noncomm_ring

theorem commutator_base_first_scalar (P Q A D : R) (hP : P*A = A*P) (hQ : Q*A = A*Q) :
    (P*D+Q)*A-A*(P*D+Q) = P*(D*A-A*D) := by
  have h := congrArg (· * D) hP
  rw [mul_assoc,mul_assoc] at h
  noncomm_ring [hP,hQ,h]

theorem commutator_base_first_differentiation (P Q D E : R) (hDE : D*E = E*D) :
    E*(P*D+Q)-(P*D+Q)*E = (E*P-P*E)*D+(E*Q-Q*E) := by
  noncomm_ring [hDE]

theorem commutator_first_zero_normal (P Q C D : R) :
    (P*D+Q)*C-C*(P*D+Q) = (P*C-C*P)*D+P*(D*C-C*D)+(Q*C-C*Q) := by
  noncomm_ring

end Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

theorem paired_normalToDivergence_base_two
    (a D Dd E μ : Module.End ℝ V) (hD : Dd = -D-μ)
    (hB : ∀ u v,B u v = B v u) (hAdj : PairedAdjoint B D Dd)
    (u : V) :
    B ((a*D*E) u) u =
      -B (a (E u)) (D u)-B ((D*a-a*D+μ*a) (E u)) u := by
  have hAdj' := hAdj.swap_of_symmetric hB
  rw [normalToDivergence_base_two a D Dd E μ hD]
  simp only [LinearMap.sub_apply,map_sub,Module.End.mul_apply,LinearMap.neg_apply,map_neg]
  rw [hAdj' _ _]

theorem paired_commutator_base_one_one
    (P Q D E Dd μ : Module.End ℝ V) (hDE : D*E = E*D) (hD : Dd = -D-μ)
    (hB : ∀ u v,B u v = B v u) (hAdj : PairedAdjoint B D Dd)
    (u : V) :
    let C := P*Q-Q*P
    B (((P*D)*(Q*E)-(Q*E)*(P*D)) u) u =
      -B (C (E u)) (D u) +
      B ((P*(D*Q-Q*D)-(D*C-C*D+μ*C)) (E u)) u -
      B ((Q*(E*P-P*E)) (D u)) u := by
  dsimp only
  rw [commutator_base_one_one P Q D E hDE]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,map_add,map_sub]
  rw [paired_normalToDivergence_base_two _ D Dd E μ hD hB hAdj u]
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,map_add,map_sub]
  ring

theorem pairedAdjoint_sub_right_replace
    {S T T' : Module.End ℝ V} (h : PairedAdjoint B S T) (h' : PairedAdjoint B S T')
    (u v : V) : B u (T v) = B u (T' v) :=
  (h u v).symm.trans (h' u v)

theorem movingTraceAdjointErrorForm_adj_congr
    (T Td L U Ud Ud' : Module.End ℝ V) (hB : ∀ u v,B u v = B v u)
    (hT : PairedAdjoint B T Td) (h : PairedAdjoint B U Ud) (h' : PairedAdjoint B U Ud') (u : V) :
    movingTraceAdjointErrorForm B T Td L U Ud u =
      movingTraceAdjointErrorForm B T Td L U Ud' u := by
  have hEq := pairedAdjoint_sub_right_replace h h'
  have hTT : B u (T (Ud u)) = B u (T (Ud' u)) := by
    have hTd := hT.swap_of_symmetric hB
    rw [← hTd u (Ud u),← hTd u (Ud' u),hEq (Td u) u]
  unfold movingTraceAdjointErrorForm
  simp only [map_sub,hEq u (T u),hEq u (U u),hTT]
  have hU : B u (U (Ud u)) = B u (U (Ud' u)) := by
    have hUd' := h'.swap_of_symmetric hB
    rw [← hUd' u (Ud u),← hUd' u (Ud' u),hEq (Ud' u) u]
  rw [hU]

end CalderonN
