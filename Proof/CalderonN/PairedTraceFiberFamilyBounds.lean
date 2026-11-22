module

public import Proof.CalderonN.PairedTraceFiberFamily
public import Proof.CalderonN.SmoothTraceSymbolCommutators

import Proof.CalderonN.ActualConormalCoefficientBounds
import Mathlib.Tactic

/-! The angular symbol closure is needed at the point. Ordinary
angular norm bounds suffice for positive base derivative orders. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

structure PairedTraceFiberFamilyBounds {hn : 3 ≤ dim} (A : SmoothTraceSymbolAtoms hn)
    (hY : IsOpen Y) (x : X dim) (β : ℝ) (N k : ℕ) (C : ℝ) (F : PairedTraceFiberFamily hn Y) : Prop where
  jets : SmoothSupportedFiberJetBound hn hY x β N k C F.forward
  symbol : SmoothTraceSymbolBounds A k C (F.forward.1 x)
  adjSymbol : SmoothTraceSymbolBounds A k C (F.reverse.1 x)

namespace PairedTraceFiberFamilyBounds

variable {hn : 3 ≤ dim} {A : SmoothTraceSymbolAtoms hn} {hY : IsOpen Y} {x : X dim}
variable {β C D : ℝ} {N k l : ℕ} {F G : PairedTraceFiberFamily hn Y}

theorem nonneg (h : PairedTraceFiberFamilyBounds A hY x β N k C F) : 0 ≤ C := h.symbol.nonneg

theorem enlarge (h : PairedTraceFiberFamilyBounds A hY x β N k C F) (hβ : 0 ≤ β) (hCD : C ≤ D) :
    PairedTraceFiberFamilyBounds A hY x β N k D F :=
  ⟨h.jets.enlarge hβ hCD,h.symbol.enlarge hCD,h.adjSymbol.enlarge hCD⟩

theorem restrict (h : PairedTraceFiberFamilyBounds A hY x β N k C F) {M : ℕ} (hMN : M ≤ N) :
    PairedTraceFiberFamilyBounds A hY x β M k C F :=
  ⟨h.jets.restrict hMN,h.symbol,h.adjSymbol⟩

theorem weaken (h : PairedTraceFiberFamilyBounds A hY x β N k C F) (hβ : 0 ≤ β) (hkl : k ≤ l) :
    PairedTraceFiberFamilyBounds A hY x β N l C F :=
  ⟨h.jets.weaken hβ h.nonneg hkl,h.symbol.weaken hkl,h.adjSymbol.weaken hkl⟩

theorem adj (h : PairedTraceFiberFamilyBounds A hY x β N k C F) (hx : x ∈ Y) (hβ : 0 ≤ β) :
    PairedTraceFiberFamilyBounds A hY x β N k C F.adj :=
  ⟨h.jets.paired hx hβ h.nonneg F.pair,h.adjSymbol,h.symbol⟩

theorem add (h : PairedTraceFiberFamilyBounds A hY x β N k C F) (hx : x ∈ Y)
    (h' : PairedTraceFiberFamilyBounds A hY x β N k D G) :
    PairedTraceFiberFamilyBounds A hY x β N k (C+D) (F.add G) :=
  ⟨h.jets.add hx h'.jets,h.symbol.add h'.symbol,h.adjSymbol.add h'.adjSymbol⟩

theorem sub (h : PairedTraceFiberFamilyBounds A hY x β N k C F) (hx : x ∈ Y)
    (h' : PairedTraceFiberFamilyBounds A hY x β N k D G) :
    PairedTraceFiberFamilyBounds A hY x β N k (C+D) (F.sub G) :=
  ⟨h.jets.sub hx h'.jets,h.symbol.sub h'.symbol,h.adjSymbol.sub h'.adjSymbol⟩

theorem mul (h : PairedTraceFiberFamilyBounds A hY x β N k C F) (hx : x ∈ Y) (hβ : 0 ≤ β)
    (h' : PairedTraceFiberFamilyBounds A hY x β N l D G) :
    PairedTraceFiberFamilyBounds A hY x β N (k+l) (max 2 ((2:ℝ)^N)*(C*D)) (F.mul hY G) := by
  have hCD := mul_nonneg h.nonneg h'.nonneg
  have h₂ := mul_le_mul_of_nonneg_right (le_max_left 2 ((2:ℝ)^N)) hCD
  have hN := mul_le_mul_of_nonneg_right (le_max_right 2 ((2:ℝ)^N)) hCD
  refine ⟨(h.jets.mul hx hβ h.nonneg h'.nonneg h'.jets).enlarge hβ hN,?_,?_⟩
  · exact (h.symbol.mul h'.symbol).enlarge (by simpa only [mul_assoc] using h₂)
  · have hr := (h'.adjSymbol.mul h.adjSymbol).enlarge
      (show 2*D*C ≤ max 2 ((2:ℝ)^N)*(C*D) from
        (show 2*D*C = 2*(C*D) by ring).le.trans h₂)
    rw [Nat.add_comm l k] at hr
    exact hr

theorem ofScalar (hx : x ∈ Y) (hβ : 0 ≤ β) {B : ℝ} (hB : 1 ≤ B)
    (hOne : SmoothTraceSymbolBounds A 0 B (1 : Module.End ℝ (SmoothSphereTrace dim)))
    (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) (hC : 0 ≤ C)
    (hf' : ∀ n ≤ N,‖iteratedFDeriv ℝ n f x‖ ≤ C*β^n) :
    PairedTraceFiberFamilyBounds A hY x β N 0 (B*C) (PairedTraceFiberFamily.scalar hY f hf) := by
  have hValue := hf' 0 (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,mul_one] at hValue
  have hs := (hOne.const_smul (f x)).enlarge
    ((mul_le_mul_of_nonneg_right hValue (zero_le_one.trans hB)).trans_eq (mul_comm C B))
  exact ⟨(SmoothSupportedFiberJetBound.ofScalar hx hβ f hf hf').enlarge hβ
    (le_mul_of_one_le_left hC hB),hs,hs⟩

theorem finite_sum {ι : Type*} (hx : x ∈ Y) (hβ : 0 ≤ β)
    (s : Finset ι) (F : ι → PairedTraceFiberFamily hn Y) (C : ι → ℝ)
    (hZero : SmoothTraceSymbolBounds A k 0 0)
    (hF : ∀ i ∈ s,PairedTraceFiberFamilyBounds A hY x β N k (C i) (F i)) :
    PairedTraceFiberFamilyBounds A hY x β N k (∑ i ∈ s,C i) (PairedTraceFiberFamily.finiteSum s F) := by
  classical
  refine ⟨?_,SmoothTraceSymbolBounds.finite_sum s _ C hZero (fun i hi => (hF i hi).symbol),
    SmoothTraceSymbolBounds.finite_sum s _ C hZero (fun i hi => (hF i hi).adjSymbol)⟩
  induction s using Finset.induction_on with
  | empty =>
    have hz : SmoothSupportedTraceFiberRegular Y (fun _ => (0 : Module.End ℝ (SmoothSphereTrace dim))) := by
      simpa only [RegularTraceFiberFamily.scalar,zero_smul] using
        (RegularTraceFiberFamily.scalar hY (fun _ => 0) contDiffOn_const).2
    have h : SmoothSupportedFiberJetBound hn hY x β N k 0 ⟨_,hz⟩ :=
      SmoothSupportedFiberJetBound.constFamily hz hx hβ le_rfl hZero.angular
    rw [Finset.sum_empty]
    apply h.congrOn hY Subset.rfl _ hx
    intro y hy
    simp only [PairedTraceFiberFamily.finiteSum,RegularTraceFiberFamily.finiteSum,Finset.sum_empty]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have h := (hF i (Finset.mem_insert_self _ _)).jets.add hx
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
    apply h.congrOn hY Subset.rfl _ hx
    intro y hy
    simp only [PairedTraceFiberFamily.finiteSum,RegularTraceFiberFamily.finiteSum,RegularTraceFiberFamily.add,Finset.sum_insert hi]

end PairedTraceFiberFamilyBounds

end CalderonN
