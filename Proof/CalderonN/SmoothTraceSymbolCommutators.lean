module

public import Proof.CalderonN.SmoothTraceAngularOrder

import Mathlib.Tactic

/-! Closure of the scalar angular commutator estimate under the sums
and products occurring in the moving trace equation. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem commutator_mul_left {R : Type*} [Ring R] (S T U : R) :
    (S*T)*U-U*(S*T) = S*(T*U-U*T)+(S*U-U*S)*T := by
  noncomm_ring

structure SmoothTraceSymbolComm (hn : 3 ≤ dim) (k : ℕ) (C : ℝ) (S T : (Module.End ℝ (SmoothSphereTrace dim))) : Prop where
  commute : k = 0 → S*T = T*S
  angular : 0 < k → SmoothTraceAngularBound hn (k-1) C (S*T-T*S)

namespace SmoothTraceSymbolComm

variable {hn : 3 ≤ dim} {k l m : ℕ} {C D E : ℝ} {S T U : (Module.End ℝ (SmoothSphereTrace dim))}

private theorem zero_bound (hn : 3 ≤ dim) (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    SmoothTraceAngularBound hn k C (0 : (Module.End ℝ (SmoothSphereTrace dim))) := by
  intro i j _ u
  simp only [LinearMap.zero_apply,traceOrderNorm,map_zero,norm_zero]
  exact mul_nonneg hC (norm_nonneg _)

theorem of_commute (hST : S*T = T*S) (hC : 0 ≤ C) : SmoothTraceSymbolComm hn k C S T := by
  refine ⟨fun _ => hST,fun _ => ?_⟩
  have h0 : S*T-T*S = (0 : Module.End ℝ (SmoothSphereTrace dim)) := sub_eq_zero.mpr hST
  rw [h0]
  exact zero_bound hn _ _ hC

theorem symm (h : SmoothTraceSymbolComm hn k C S T) : SmoothTraceSymbolComm hn k C T S := by
  refine ⟨fun hk => (h.commute hk).symm,fun hk => ?_⟩
  intro i j hij u
  have hb := h.angular hk i j hij u
  have hEq : T*S-S*T = -(S*T-T*S) := by abel
  simpa only [hEq,LinearMap.neg_apply,traceOrderNorm,map_neg,norm_neg] using hb

theorem weaken (h : SmoothTraceSymbolComm hn k C S T) (hkl : k ≤ l) (hC : 0 ≤ C) :
    SmoothTraceSymbolComm hn l C S T := by
  by_cases hk : k = 0
  · exact of_commute (h.commute hk) hC
  · refine ⟨fun hl => by omega,fun _ => ?_⟩
    exact (h.angular (by omega)).weaken hC (by omega)

theorem add_left (hS : SmoothTraceSymbolComm hn k C S U) (hT : SmoothTraceSymbolComm hn k D T U) :
    SmoothTraceSymbolComm hn k (C+D) (S+T) U := by
  refine ⟨fun hk => ?_,fun hk => ?_⟩
  · simp only [add_mul,mul_add,hS.commute hk,hT.commute hk]
  · rw [show (S+T)*U-U*(S+T) = (S*U-U*S)+(T*U-U*T) by noncomm_ring]
    exact (hS.angular hk).add (hT.angular hk)

theorem smul_left (h : SmoothTraceSymbolComm hn k C S T) (a : ℝ) :
    SmoothTraceSymbolComm hn k (|a| * C) (a • S) T := by
  refine ⟨fun hk => ?_,fun hk => ?_⟩
  · rw [smul_mul_assoc,mul_smul_comm,h.commute hk]
  · have he : (a • S)*T-T*(a • S) = a • (S*T-T*S) := by
      ext u : 1
      simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_smul,smul_sub]
    rw [he]
    exact (h.angular hk).const_smul a

theorem mul_left (hS : SmoothTraceSymbolComm hn (k+m) (C*E) S U)
    (hT : SmoothTraceSymbolComm hn (l+m) (D*E) T U)
    (hSB : SmoothTraceAngularBound hn k C S) (hTB : SmoothTraceAngularBound hn l D T)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    SmoothTraceSymbolComm hn (k+l+m) ((2*C*D)*E) (S*T) U := by
  refine ⟨fun hz => ?_,fun hpos => ?_⟩
  · have h₁ := hS.commute (by omega)
    have h₂ := hT.commute (by omega)
    calc
      S*T*U = S*(T*U) := mul_assoc _ _ _
      _ = S*(U*T) := by rw [h₂]
      _ = (S*U)*T := (mul_assoc _ _ _).symm
      _ = (U*S)*T := by rw [h₁]
      _ = U*(S*T) := mul_assoc _ _ _
  rw [commutator_mul_left S T U]
  have h₁ : SmoothTraceAngularBound hn (k+l+m-1) (C*(D*E)) (S*(T*U-U*T)) := by
    by_cases hl : l+m = 0
    · have h0 : T*U-U*T = (0 : Module.End ℝ (SmoothSphereTrace dim)) := sub_eq_zero.mpr (hT.commute hl)
      rw [h0,mul_zero]
      exact zero_bound hn _ _ (by positivity)
    · have he : k+(l+m-1) = k+l+m-1 := by omega
      rw [← he]
      exact hSB.mul (hT.angular (by omega)) hC
  have h₂ : SmoothTraceAngularBound hn (k+l+m-1) ((C*E)*D) ((S*U-U*S)*T) := by
    by_cases hk : k+m = 0
    · have h0 : S*U-U*S = (0 : Module.End ℝ (SmoothSphereTrace dim)) := sub_eq_zero.mpr (hS.commute hk)
      rw [h0,zero_mul]
      exact zero_bound hn _ _ (by positivity)
    · have he : (k+m-1)+l = k+l+m-1 := by omega
      rw [← he]
      exact (hS.angular (by omega)).mul hTB (by positivity)
  convert h₁.add h₂ using 1
  ring

end SmoothTraceSymbolComm

/-- The checked atoms come with an angular estimate and pairwise
commutator estimates. The expression constant includes the factors
introduced by the product rule. -/
structure SmoothTraceSymbolAtoms (hn : 3 ≤ dim) where
  atom : ℕ → ℝ → (Module.End ℝ (SmoothSphereTrace dim)) → Prop
  nonneg : ∀ {k C S},atom k C S → 0 ≤ C
  angular : ∀ {k C S},atom k C S → SmoothTraceAngularBound hn k C S
  comm : ∀ {k l C D S T},atom k C S → atom l D T → SmoothTraceSymbolComm hn (k+l) (C*D) S T

inductive SmoothTraceSymbolBounds {hn : 3 ≤ dim} (A : SmoothTraceSymbolAtoms hn) :
    ℕ → ℝ → (Module.End ℝ (SmoothSphereTrace dim)) → Prop
  | atom {k C S} : A.atom k C S → SmoothTraceSymbolBounds A k C S
  | add {k C D S T} :
      SmoothTraceSymbolBounds A k C S → SmoothTraceSymbolBounds A k D T →
      SmoothTraceSymbolBounds A k (C+D) (S+T)
  | mul {k l C D S T} :
      SmoothTraceSymbolBounds A k C S → SmoothTraceSymbolBounds A l D T →
      SmoothTraceSymbolBounds A (k+l) (2*C*D) (S*T)
  | const_smul {k C S} (a : ℝ) :
      SmoothTraceSymbolBounds A k C S → SmoothTraceSymbolBounds A k (|a| * C) (a • S)
  | weaken {k l C S} :
      SmoothTraceSymbolBounds A k C S → k ≤ l → SmoothTraceSymbolBounds A l C S
  | enlarge {k C D S} :
      SmoothTraceSymbolBounds A k C S → C ≤ D → SmoothTraceSymbolBounds A k D S

namespace SmoothTraceSymbolBounds

variable {hn : 3 ≤ dim} {A : SmoothTraceSymbolAtoms hn}
variable {k l : ℕ} {C D : ℝ} {S T : (Module.End ℝ (SmoothSphereTrace dim))}

theorem nonneg (h : SmoothTraceSymbolBounds A k C S) : 0 ≤ C := by
  induction h with
  | atom h => exact A.nonneg h
  | add _ _ ha hb => exact add_nonneg ha hb
  | mul _ _ ha hb => exact mul_nonneg (mul_nonneg (by norm_num) ha) hb
  | const_smul a _ h => exact mul_nonneg (abs_nonneg a) h
  | weaken _ _ h => exact h
  | enlarge _ hCD h => exact h.trans hCD

theorem angular (h : SmoothTraceSymbolBounds A k C S) : SmoothTraceAngularBound hn k C S := by
  induction h with
  | atom h => exact A.angular h
  | add _ _ ha hb => exact ha.add hb
  | mul hS hT ha hb =>
    have h₀ := hS.nonneg
    have h₁ := hT.nonneg
    exact (ha.mul hb h₀).enlarge (by nlinarith only [mul_nonneg h₀ h₁])
  | const_smul a _ h => exact h.const_smul a
  | weaken h₀ hkl ha => exact ha.weaken h₀.nonneg hkl
  | enlarge _ hCD h => exact h.enlarge hCD

theorem sub (hS : SmoothTraceSymbolBounds A k C S) (hT : SmoothTraceSymbolBounds A k D T) :
    SmoothTraceSymbolBounds A k (C+D) (S-T) := by
  have h := hS.add (hT.const_smul (-1))
  have he : S-T = S+(-1:ℝ) • T := by
    ext u : 1
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,neg_one_smul,sub_eq_add_neg]
  rw [he]
  simpa only [abs_neg,abs_one,one_mul] using h

theorem zero_of_identity (h : SmoothTraceSymbolBounds A 0 C (1 : Module.End ℝ (SmoothSphereTrace dim)))
    (k : ℕ) : SmoothTraceSymbolBounds A k 0 0 := by
  have h' := (h.const_smul 0).weaken (Nat.zero_le k)
  simpa only [abs_zero,zero_mul,zero_smul] using h'

theorem finite_sum {ι : Type*} (s : Finset ι) (F : ι → Module.End ℝ (SmoothSphereTrace dim))
    (C : ι → ℝ) (hZero : SmoothTraceSymbolBounds A k 0 0)
    (hF : ∀ i ∈ s,SmoothTraceSymbolBounds A k (C i) (F i)) :
    SmoothTraceSymbolBounds A k (∑ i ∈ s,C i) (∑ i ∈ s,F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using hZero
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

private theorem comm_enlarge (hS : SmoothTraceSymbolComm hn k C S T) (hCD : C ≤ D) :
    SmoothTraceSymbolComm hn k D S T :=
  ⟨hS.commute,fun hk => (hS.angular hk).enlarge hCD⟩

theorem comm_atom (hS : SmoothTraceSymbolBounds A k C S) (hT : A.atom l D T) :
    SmoothTraceSymbolComm hn (k+l) (C*D) S T := by
  have hD := A.nonneg hT
  induction hS with
  | atom hS => exact A.comm hS hT
  | add _ _ h₁ h₂ =>
    rw [add_mul]
    exact h₁.add_left h₂
  | mul h₁ h₂ h₁' h₂' => exact h₁'.mul_left h₂' h₁.angular h₂.angular h₁.nonneg h₂.nonneg hD
  | const_smul a _ h =>
    rw [mul_assoc]
    exact h.smul_left a
  | weaken h₀ hkl h =>
    exact h.weaken (Nat.add_le_add_right hkl _) (mul_nonneg h₀.nonneg hD)
  | enlarge _ hC h =>
    exact comm_enlarge h (mul_le_mul_of_nonneg_right hC hD)

theorem comm (hS : SmoothTraceSymbolBounds A k C S) (hT : SmoothTraceSymbolBounds A l D T) :
    SmoothTraceSymbolComm hn (k+l) (C*D) S T := by
  have hC := hS.nonneg
  have h (l₀ : ℕ) (D₀ : ℝ) (T₀ : (Module.End ℝ (SmoothSphereTrace dim))) (hT₀ : SmoothTraceSymbolBounds A l₀ D₀ T₀) :
      SmoothTraceSymbolComm hn (l₀+k) (D₀*C) T₀ S := by
    induction hT₀ with
    | atom hT₀ =>
      rw [Nat.add_comm,mul_comm]
      exact (hS.comm_atom hT₀).symm
    | add _ _ h₁ h₂ =>
      rw [add_mul]
      exact h₁.add_left h₂
    | mul h₁ h₂ h₁' h₂' =>
      exact h₁'.mul_left h₂' h₁.angular h₂.angular h₁.nonneg h₂.nonneg hC
    | const_smul a _ h =>
      rw [mul_assoc]
      exact h.smul_left a
    | weaken h₀ hkl h =>
      exact h.weaken (Nat.add_le_add_right hkl _) (mul_nonneg h₀.nonneg hC)
    | enlarge _ hD h =>
      exact comm_enlarge h (mul_le_mul_of_nonneg_right hD hC)
  rw [Nat.add_comm,mul_comm]
  exact (h l D T hT).symm

end SmoothTraceSymbolBounds

end CalderonN
