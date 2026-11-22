module

public import Proof.CalderonN.SmoothTraceDualOrder

import Mathlib.Tactic

/-! Angular operator bounds on the four half-integer Sobolev levels
used by the moving trace error form. -/

public section

noncomputable section
open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def traceOrderExponent (i : Fin 4) : ℝ := (i.val:ℝ)-3/2

theorem traceOrderExponent_le (i : Fin 4) : traceOrderExponent i ≤ 2 := by
  have hi : i.val ≤ 3 := Nat.le_of_lt_succ i.isLt
  have hi' : (i.val:ℝ) ≤ 3 := by exact_mod_cast hi
  unfold traceOrderExponent
  linarith

theorem traceOrderExponent_rev (i : Fin 4) : traceOrderExponent i.rev = -traceOrderExponent i := by
  have hi : i.val ≤ 3 := Nat.le_of_lt_succ i.isLt
  have hRev : i.rev.val = 3-i.val := by rw [Fin.val_rev]; omega
  rw [traceOrderExponent, hRev, Nat.cast_sub hi]
  unfold traceOrderExponent
  push_cast
  ring

@[expose] def traceOrderNorm (hn : 3 ≤ dim) (i : Fin 4) (u : SmoothSphereTrace dim) : ℝ :=
  ‖smoothSphereTraceSobolev hn (traceOrderExponent i) (traceOrderExponent_le i) u‖

@[expose] def SmoothTraceAngularBound (hn : 3 ≤ dim) (order : ℕ) (C : ℝ)
    (T : Module.End ℝ (SmoothSphereTrace dim)) : Prop :=
  ∀ (i j : Fin 4), j.val = i.val+order → ∀ u, traceOrderNorm hn i (T u) ≤ C*traceOrderNorm hn j u

namespace SmoothTraceAngularBound

variable {hn : 3 ≤ dim} {order a b : ℕ} {C D : ℝ}
variable {S T : Module.End ℝ (SmoothSphereTrace dim)}

theorem add (hS : SmoothTraceAngularBound hn order C S) (hT : SmoothTraceAngularBound hn order D T) :
    SmoothTraceAngularBound hn order (C+D) (S+T) := by
  intro i j hij u
  have h := add_le_add (hS i j hij u) (hT i j hij u)
  simp only [traceOrderNorm,LinearMap.add_apply,map_add] at *
  exact (norm_add_le _ _).trans (h.trans_eq (by ring))

theorem const_smul (hT : SmoothTraceAngularBound hn order C T) (c : ℝ) :
    SmoothTraceAngularBound hn order (|c| * C) (c • T) := by
  intro i j hij u
  have h := mul_le_mul_of_nonneg_left (hT i j hij u) (abs_nonneg c)
  simpa [traceOrderNorm,norm_smul,Real.norm_eq_abs,mul_assoc] using h

theorem sub (hS : SmoothTraceAngularBound hn order C S) (hT : SmoothTraceAngularBound hn order D T) :
    SmoothTraceAngularBound hn order (C+D) (S-T) := by
  have h := hS.add (hT.const_smul (-1))
  simpa [sub_eq_add_neg] using h

theorem mul (hS : SmoothTraceAngularBound hn a C S) (hT : SmoothTraceAngularBound hn b D T)
    (hC : 0 ≤ C) :
    SmoothTraceAngularBound hn (a+b) (C*D) (S*T) := by
  intro i j hij u
  let k : Fin 4 := ⟨i.val+a,by have := j.isLt; omega⟩
  exact (hS i k rfl (T u)).trans
    ((mul_le_mul_of_nonneg_left (hT k j (by dsimp only [k]; omega) u) hC).trans_eq (by ring))

theorem weaken (hT : SmoothTraceAngularBound hn a C T) (hC : 0 ≤ C) (hab : a ≤ b) :
    SmoothTraceAngularBound hn b C T := by
  intro i j hij u
  let k : Fin 4 := ⟨i.val+a,by have := j.isLt; omega⟩
  have hkj : traceOrderExponent k ≤ traceOrderExponent j := by
    unfold traceOrderExponent
    apply sub_le_sub_right
    exact_mod_cast (show k.val ≤ j.val by dsimp only [k]; omega)
  exact (hT i k rfl u).trans
    (mul_le_mul_of_nonneg_left (norm_smoothSphereTraceSobolev_mono hn _ _ (traceOrderExponent_le k) (traceOrderExponent_le j) hkj u) hC)

theorem enlarge (hT : SmoothTraceAngularBound hn order C T) (hCD : C ≤ D) :
    SmoothTraceAngularBound hn order D T := by
  intro i j hij u
  exact (hT i j hij u).trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))

theorem adjoint (hT : SmoothTraceAngularBound hn order C T) (hC : 0 ≤ C)
    (hAdj : SmoothTraceAdjoint hn T S) :
    SmoothTraceAngularBound hn order C S := by
  intro i j hij u
  have hRev : i.rev.val = j.rev.val+order := by
    simp only [Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hNeg (k : Fin 4) : -traceOrderExponent k.rev = traceOrderExponent k := by
    rw [traceOrderExponent_rev,neg_neg]
  have h := norm_smoothTrace_adjoint_of_bound hn (traceOrderExponent i.rev) (traceOrderExponent j.rev)
    (traceOrderExponent_le i.rev) (traceOrderExponent_le j.rev)
    (by rw [hNeg]; exact traceOrderExponent_le i)
    (by rw [hNeg]; exact traceOrderExponent_le j)
    T S hAdj C hC (hT j.rev i.rev hRev) u
  rw [smoothSphereTraceSobolev_order_eq hn (hNeg j) _ (traceOrderExponent_le j),
    smoothSphereTraceSobolev_order_eq hn (hNeg i) _ (traceOrderExponent_le i)] at h
  exact h

theorem abs_pair_le (hT : SmoothTraceAngularBound hn order C T)
    (i j : Fin 4) (hij : j.val = i.val+order) (u v : SmoothSphereTrace dim) :
    |⟪smoothSphereTraceL2 hn (T u),smoothSphereTraceL2 hn v⟫_ℝ| ≤
      C*traceOrderNorm hn j u*traceOrderNorm hn i.rev v := by
  have hNeg : -traceOrderExponent i.rev = traceOrderExponent i := by
    rw [traceOrderExponent_rev,neg_neg]
  have h := abs_smoothTrace_inner_le_sobolev hn (traceOrderExponent i.rev) (traceOrderExponent_le i.rev)
    (by rw [hNeg]; exact traceOrderExponent_le i) (T u) v
  rw [smoothSphereTraceSobolev_order_eq hn hNeg _ (traceOrderExponent_le i)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hT i j hij u) (norm_nonneg _))

end SmoothTraceAngularBound

end CalderonN
