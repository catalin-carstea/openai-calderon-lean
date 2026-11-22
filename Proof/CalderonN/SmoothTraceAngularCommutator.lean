module

public import Proof.CalderonN.SmoothTraceAngularOrder
public import Proof.CalderonN.SmoothTraceDegreeSpectral

import Proof.CalderonN.SmoothTraceRotationGraph
import Mathlib.Tactic

/-! First-order generators on the common smooth trace space, and the
product estimates that preserve one commutator order of cancellation. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

section
variable {R : Type*} [Ring R]

theorem operator_comm_mul_right (A B C : R) :
    A*(B*C)-(B*C)*A = (A*B-B*A)*C+B*(A*C-C*A) := by noncomm_ring

theorem operator_comm_mul_left (A B C : R) :
    (A*B)*C-C*(A*B) = A*(B*C-C*B)+(A*C-C*A)*B := by noncomm_ring

end

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothTraceDegree_angularBound (hn : 3 ≤ dim)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hSym : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f)) :
    SmoothTraceAngularBound hn 1 1 B := by
  intro i j hij u
  have he : traceOrderExponent i+1 = traceOrderExponent j := by
    unfold traceOrderExponent
    have h : (j.val:ℝ) = (i.val:ℝ)+1 := by exact_mod_cast hij
    linarith
  have hb : traceOrderExponent i+1 ≤ 2 := he.symm ▸ traceOrderExponent_le j
  have h := norm_smoothTraceDegree_le hSym hFin (traceOrderExponent i) hb u
  rw [smoothSphereTraceSobolev_order_eq hn he hb (traceOrderExponent_le j)] at h
  simpa only [traceOrderNorm,one_mul] using h

theorem smoothTraceRotation_angularBound (hn : 3 ≤ dim) (i j : Fin dim) :
    SmoothTraceAngularBound hn 1 (2*(dim:ℝ)) (smoothSphereTraceRotation i j) := by
  intro a b hab u
  have he : traceOrderExponent a+1 = traceOrderExponent b := by
    unfold traceOrderExponent
    have h : (b.val:ℝ) = (a.val:ℝ)+1 := by exact_mod_cast hab
    linarith
  have hb : traceOrderExponent a+1 ≤ 2 := he.symm ▸ traceOrderExponent_le b
  have h := norm_smoothSphereTraceRotation_le hn (traceOrderExponent a) hb i j u
  rw [smoothSphereTraceSobolev_order_eq hn he hb (traceOrderExponent_le b)] at h
  exact h

namespace SmoothTraceAngularBound

variable {hn : 3 ≤ dim}
variable {A B C : Module.End ℝ (SmoothSphereTrace dim)}
variable {a b c k l : ℕ} {U V X Y : ℝ}

theorem comm_mul_right
    (hB : SmoothTraceAngularBound hn b U B) (hC : SmoothTraceAngularBound hn c V C)
    (hAB : SmoothTraceAngularBound hn k X (A*B-B*A)) (hAC : SmoothTraceAngularBound hn l Y (A*C-C*A))
    (hOrd : k+c = b+l) (hX : 0 ≤ X) (hU : 0 ≤ U) :
    SmoothTraceAngularBound hn (k+c) (X*V+U*Y) (A*(B*C)-(B*C)*A) := by
  rw [operator_comm_mul_right A B C]
  have h1 := hAB.mul hC hX
  have h2 := hB.mul hAC hU
  rw [← hOrd] at h2
  exact h1.add h2

theorem comm_mul_left
    (hA : SmoothTraceAngularBound hn a U A) (hB : SmoothTraceAngularBound hn b V B)
    (hAC : SmoothTraceAngularBound hn k X (A*C-C*A)) (hBC : SmoothTraceAngularBound hn l Y (B*C-C*B))
    (hOrd : a+l = k+b) (hU : 0 ≤ U) (hX : 0 ≤ X) :
    SmoothTraceAngularBound hn (a+l) (U*Y+X*V) ((A*B)*C-C*(A*B)) := by
  rw [operator_comm_mul_left A B C]
  have h1 := hA.mul hBC hU
  have h2 := hAC.mul hB hX
  rw [← hOrd] at h2
  exact h1.add h2

/-- The principal commutator of two products of first-order angular
operators has order three given the four genuine generator commutators. -/
theorem comm_firstOrder_products
    {D : Module.End ℝ (SmoothSphereTrace dim)} {C₀ D₀ AC BC AD BD : ℝ}
    (hA : SmoothTraceAngularBound hn 1 U A) (hB : SmoothTraceAngularBound hn 1 V B)
    (hC : SmoothTraceAngularBound hn 1 C₀ C) (hD : SmoothTraceAngularBound hn 1 D₀ D)
    (hAC : SmoothTraceAngularBound hn 1 AC (A*C-C*A)) (hAD : SmoothTraceAngularBound hn 1 AD (A*D-D*A))
    (hBC : SmoothTraceAngularBound hn 1 BC (B*C-C*B)) (hBD : SmoothTraceAngularBound hn 1 BD (B*D-D*B))
    (hU : 0 ≤ U) (hC₀ : 0 ≤ C₀) (hD₀ : 0 ≤ D₀) (hAC₀ : 0 ≤ AC) (hAD₀ : 0 ≤ AD)
    (hBC₀ : 0 ≤ BC) :
    SmoothTraceAngularBound hn 3 (U*(BC*D₀+C₀*BD)+(AC*D₀+C₀*AD)*V)
      ((A*B)*(C*D)-(C*D)*(A*B)) :=
  comm_mul_left hA hB
    (hC.comm_mul_right hD hAC hAD rfl hAC₀ hC₀)
    (hC.comm_mul_right hD hBC hBD rfl hBC₀ hC₀) rfl hU
    (add_nonneg (mul_nonneg hAC₀ hD₀) (mul_nonneg hC₀ hAD₀))

end SmoothTraceAngularBound

end CalderonN
