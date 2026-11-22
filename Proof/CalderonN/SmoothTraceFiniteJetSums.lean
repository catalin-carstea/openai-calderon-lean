module

public import Proof.CalderonN.SmoothTraceNegation

import Proof.CalderonN.ActualConormalCoefficientBounds
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

theorem RegularTraceFiberFamily.iteratedDerivative_neg
    (hY : IsOpen Y) (F : RegularTraceFiberFamily Y) (n : ℕ) (a : Fin n → X dim) {x : X dim} (hx : x ∈ Y) :
    (F.neg.iteratedDerivative hY n a).1 x = -((F.iteratedDerivative hY n a).1 x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    let G := F.iteratedDerivative hY n (Fin.tail a)
    let H := F.neg.iteratedDerivative hY n (Fin.tail a)
    have hEq : H.1 =ᶠ[𝓝 x] G.neg.1 := by
      filter_upwards [hY.mem_nhds hx] with y hy
      exact ih (Fin.tail a) hy
    change (H.derivative hY (a 0)).1 x = -((G.derivative hY (a 0)).1 x)
    rw [show (H.derivative hY (a 0)).1 x = (G.neg.derivative hY (a 0)).1 x from
      smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq hY H.2 G.neg.2 (a 0) hx hEq]
    exact G.derivative_neg_value hY (a 0) hx

namespace SmoothSupportedFiberJetBound

variable {hY : IsOpen Y} {x : X dim} {β C : ℝ} {N k : ℕ} {F : RegularTraceFiberFamily Y}

theorem neg (h : SmoothSupportedFiberJetBound hn hY x β N k C F) (hx : x ∈ Y) :
    SmoothSupportedFiberJetBound hn hY x β N k C F.neg := by
  intro n hnN a ha
  rw [F.iteratedDerivative_neg hY n a hx]
  exact (h n hnN a ha).neg

theorem finite_sum {ι : Type*} (hx : x ∈ Y) (hβ : 0 ≤ β)
    (s : Finset ι) (F : ι → RegularTraceFiberFamily Y) (C : ι → ℝ)
    (hF : ∀ i ∈ s,SmoothSupportedFiberJetBound hn hY x β N k (C i) (F i)) :
    SmoothSupportedFiberJetBound hn hY x β N k (∑ i ∈ s,C i) (RegularTraceFiberFamily.finiteSum s F) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : SmoothSupportedTraceFiberRegular Y (fun _ => (0 : Module.End ℝ (SmoothSphereTrace dim))) := by
      simpa only [RegularTraceFiberFamily.scalar,zero_smul] using
        (RegularTraceFiberFamily.scalar hY (fun _ => 0) contDiffOn_const).2
    have h : SmoothSupportedFiberJetBound hn hY x β N k 0 ⟨_,hz⟩ :=
      constFamily hz hx hβ le_rfl (smoothTraceAngularBound_zero hn k le_rfl)
    rw [Finset.sum_empty]
    apply h.congrOn hY Subset.rfl _ hx
    intro y hy
    simp only [RegularTraceFiberFamily.finiteSum,Finset.sum_empty]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have h := (hF i (Finset.mem_insert_self _ _)).add hx (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
    apply h.congrOn hY Subset.rfl _ hx
    intro y hy
    simp only [RegularTraceFiberFamily.finiteSum,RegularTraceFiberFamily.add,Finset.sum_insert hi]

end SmoothSupportedFiberJetBound

end CalderonN
