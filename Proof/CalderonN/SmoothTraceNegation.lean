module

public import Proof.CalderonN.PairedTraceFiberFamilyBounds

import Mathlib.Tactic

public section

noncomputable section
open Set
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

theorem SmoothTraceAngularBound.neg {k : ℕ} {C : ℝ} {T : Module.End ℝ (SmoothSphereTrace dim)}
    (h : SmoothTraceAngularBound hn k C T) :
    SmoothTraceAngularBound hn k C (-T) := by
  intro i j hij u
  simpa only [traceOrderNorm,LinearMap.neg_apply,map_neg,norm_neg] using h i j hij u

theorem SmoothTraceSymbolBounds.neg {A : SmoothTraceSymbolAtoms hn} {k : ℕ} {C : ℝ}
    {T : Module.End ℝ (SmoothSphereTrace dim)} (h : SmoothTraceSymbolBounds A k C T) :
    SmoothTraceSymbolBounds A k C (-T) := by
  have h' := h.const_smul (-1:ℝ)
  have he : (-1:ℝ) • T = -T := by
    ext u : 1
    simp only [LinearMap.smul_apply,LinearMap.neg_apply,neg_one_smul]
  simpa only [he,abs_neg,abs_one,one_mul] using h'

private theorem commutator_neg_right {R : Type*} [Ring R] (D P : R) :
    D*(-P)-(-P)*D = -(D*P-P*D) := by noncomm_ring

theorem RegularTraceFiberFamily.derivative_neg_value
    (hY : IsOpen Y) (F : RegularTraceFiberFamily Y) (a : X dim) {x : X dim} (hx : x ∈ Y) :
    ((F.neg.derivative hY a).1 x) = -((F.derivative hY a).1 x) := by
  ext u : 1
  obtain ⟨v,rfl⟩ := smoothSupportedTraceFiberL_surjective_of_mem hY hx u
  rw [← action_fiber hY (F.neg.derivative hY a) v x,LinearMap.neg_apply,
    ← action_fiber hY (F.derivative hY a) v x,← map_neg]
  simp only [action_derivative,action_neg]
  rw [commutator_neg_right (smoothSupportedTraceBaseDiff (Y:=Y) a) (F.action hY)]
  rw [LinearMap.neg_apply]

end CalderonN
