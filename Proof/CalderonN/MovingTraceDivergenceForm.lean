module

public import Proof.CalderonN.MovingTraceTwoComponentComparison
public import Proof.CalderonN.MovingTraceBaseCommutators
public import Proof.CalderonN.SmoothSupportedTraceAdjointCalculus

import Mathlib.Tactic

/-! The second base derivatives can be placed in divergence form before
integrating the commutator. Each remaining term has at most one base
derivative on either argument. -/

public section

set_option autoImplicit false
namespace CalderonN

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}

theorem PairedAdjoint.swap_of_symmetric {S T : Module.End ℝ V}
    (h : PairedAdjoint B S T) (hB : ∀ u v,B u v = B v u) : PairedAdjoint B T S :=
  fun u v => (hB _ _).trans ((h v u).symm.trans (hB _ _))

theorem paired_commutator_divergence_form
    (S Sd D Dd E a : Module.End ℝ V)
    (hB : ∀ u v,B u v = B v u) (hS : PairedAdjoint B S Sd) (hD : PairedAdjoint B D Dd)
    (u : V) :
    B ((S*(Dd*a*E)-(Dd*a*E)*S) u) u =
      B ((a*E) u) ((D*Sd-Sd*D) u) +
        B (((S*a-a*S)*E) u) (D u) +
        B ((a*(S*E-E*S)) u) (D u) := by
  have hDd := hD.swap_of_symmetric hB
  have hCross : PairedAdjoint B (S*Dd-Dd*S) (D*Sd-Sd*D) :=
    (hS.mul hDd).sub (hDd.mul hS)
  rw [show S*(Dd*a*E)-(Dd*a*E)*S =
    (S*Dd-Dd*S)*(a*E)+Dd*((S*a-a*S)*E)+Dd*(a*(S*E-E*S)) by noncomm_ring]
  simp only [LinearMap.add_apply,map_add,Module.End.mul_apply]
  rw [hCross _ _,hDd _ _,hDd _ _]

theorem paired_product_divergence_form
    (D Dd E a Z : Module.End ℝ V)
    (hB : ∀ u v,B u v = B v u) (hD : PairedAdjoint B D Dd) (u : V) :
    B ((Dd*a*E*Z) u) u =
      B ((a*Z*E) u) (D u)+B ((a*(E*Z-Z*E)) u) (D u) := by
  have hDd := hD.swap_of_symmetric hB
  rw [show Dd*a*E*Z = Dd*(a*Z*E)+Dd*(a*(E*Z-Z*E)) by noncomm_ring]
  simp only [LinearMap.add_apply,map_add,Module.End.mul_apply]
  rw [hDd _ _,hDd _ _]

theorem paired_movingTraceAdjointErrorForm_reduce
    (T Td L U Ud : Module.End ℝ V) (u : V)
    (hB : ∀ u v,B u v = B v u) (hT : PairedAdjoint B T Td) (hU : PairedAdjoint B U Ud) :
    movingTraceAdjointErrorForm B T Td L U Ud u =
      4*B ((Td*U-U*Td) u) u+B (((Ud-U)*U-U*(Ud-U)) u) u-4*B ((U*(L-Td)) u) u := by
  have hTd := hT.swap_of_symmetric hB
  have hUd := hU.swap_of_symmetric hB
  have hTU : PairedAdjoint B (Td*U-U*Td) (Ud*T-T*Ud) :=
    (hTd.mul hU).sub (hU.mul hTd)
  have hComm : (Ud-U)*U-U*(Ud-U) = Ud*U-U*Ud := by noncomm_ring
  rw [movingTraceAdjointErrorForm,hComm]
  have h₁ : B u (Td (U u)-U (Td u)) = B ((Td*U-U*Td) u) u := hB _ _
  have h₂ : B u (Ud (T u)-T (Ud u)) = B ((Td*U-U*Td) u) u := (hTU u u).symm
  have h₃ : B u (Ud (U u)-U (Ud u)) = B ((Ud*U-U*Ud) u) u := hB _ _
  rw [h₁,h₂,h₃,hB u (U ((L-Td) u))]
  change _ = 4*B ((Td*U-U*Td) u) u+B ((Ud*U-U*Ud) u) u-4*B (U ((L-Td) u)) u
  ring

end CalderonN
