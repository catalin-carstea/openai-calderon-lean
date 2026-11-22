module

public import Proof.CalderonN.CoordinateTraceDivergence

import Mathlib.Tactic

/-! A regular coordinate first-order model admits the explicit
adjoint obtained from the base integration by parts. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

private theorem firstOrderAdjoint_mul {R : Type*} [Ring R] (D L F : R) :
    (-D-L)*F = (-F)*D-((D*F-F*D)+L*F) := by noncomm_ring

namespace CoordinateTraceFirstOrder

@[expose] def neg (S : CoordinateTraceFirstOrder Y) : CoordinateTraceFirstOrder Y :=
  ⟨fun i => (S.first i).neg,S.zero.neg⟩

theorem neg_action (hY : IsOpen Y) (S : CoordinateTraceFirstOrder Y) :
    S.neg.action hY = -S.action hY := by
  unfold neg action
  ext u : 1
  simp only [RegularTraceFiberFamily.action_neg,LinearMap.add_apply,LinearMap.neg_apply,
    LinearMap.sum_apply,Module.End.mul_apply,Finset.sum_neg_distrib]
  abel

@[expose] def ofPaired (P : I dim → PairedTraceFiberFamily hn Y) (Q : PairedTraceFiberFamily hn Y) :
    CoordinateTraceFirstOrder Y :=
  ⟨fun i => (P i).forward,Q.forward⟩

@[expose] def adjointCorrection (hY : IsOpen Y) (density : I dim → RegularTraceFiberFamily Y)
    (P : I dim → PairedTraceFiberFamily hn Y) : RegularTraceFiberFamily Y :=
  (RegularTraceFiberFamily.finiteSum Finset.univ (fun i =>
    ((P i).reverse.derivative hY (axis i)).add ((density i).mul hY (P i).reverse))).neg

@[expose] def ofPairedAdjoint (hY : IsOpen Y) (density : I dim → RegularTraceFiberFamily Y)
    (P : I dim → PairedTraceFiberFamily hn Y) (Q : PairedTraceFiberFamily hn Y) :
    CoordinateTraceFirstOrder Y :=
  ⟨fun i => (P i).reverse.neg,Q.reverse.add (adjointCorrection hY density P)⟩

theorem paired_ofPaired (hY : IsOpen Y) (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
    (density : I dim → RegularTraceFiberFamily Y)
    (P : I dim → PairedTraceFiberFamily hn Y) (Q : PairedTraceFiberFamily hn Y)
    (hD : ∀ i,PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) (smoothSupportedTraceBaseDiff (axis i))
      (-smoothSupportedTraceBaseDiff (axis i)-(density i).action hY)) :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) ((ofPaired P Q).action hY)
      ((ofPairedAdjoint hY density P Q).action hY) := by
  let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let F (i : I dim) := (-D i-(density i).action hY)*(P i).reverse.action hY
  have h := (PairedAdjoint.sum Finset.univ (fun i => (P i).forward.action hY*D i) F (fun i _ =>
    ((P i).pairedAction hY μ hμ).mul (hD i))).add (Q.pairedAction hY μ hμ)
  have hSum (i : I dim) : F i = (P i).reverse.neg.action hY*D i-
      ((((P i).reverse.derivative hY (axis i)).add ((density i).mul hY (P i).reverse)).action hY) := by
    simp only [RegularTraceFiberFamily.action_derivative,RegularTraceFiberFamily.action_mul,
      RegularTraceFiberFamily.action_add,RegularTraceFiberFamily.action_neg,F]
    exact firstOrderAdjoint_mul (D i) ((density i).action hY) ((P i).reverse.action hY)
  have hSum' := congrArg (∑ i : I dim, · i) (funext hSum)
  dsimp only at hSum'
  rw [Finset.sum_sub_distrib (fun i => (P i).reverse.neg.action hY*D i)
    (fun i => (((P i).reverse.derivative hY (axis i)).add ((density i).mul hY (P i).reverse)).action hY)] at hSum'
  have he : (∑ i,F i)+Q.reverse.action hY = (ofPairedAdjoint hY density P Q).action hY := by
    rw [hSum']
    simp only [ofPairedAdjoint,action,adjointCorrection,RegularTraceFiberFamily.action_finiteSum,
      RegularTraceFiberFamily.action_add,RegularTraceFiberFamily.action_neg]
    abel
  rw [he] at h
  exact h

end CoordinateTraceFirstOrder

theorem movingTraceAdjointErrorForm_modelAdjoint_congr {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (T Td Td' L U Ud : Module.End ℝ V) (u : V)
    (hSym : ∀ x y,B x y = B y x) (hT : PairedAdjoint B T Td) (hT' : PairedAdjoint B T Td')
    (hU : PairedAdjoint B U Ud) :
    movingTraceAdjointErrorForm B T Td L U Ud u =
      movingTraceAdjointErrorForm B T Td' (Td'+(L-Td)) U Ud u := by
  rw [paired_movingTraceAdjointErrorForm_reduce _ _ _ _ _ _ hSym hT hU,
    paired_movingTraceAdjointErrorForm_reduce _ _ _ _ _ _ hSym hT' hU]
  have hL : Td'+(L-Td)-Td' = L-Td := by abel
  rw [hL]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  have hEq (v w : V) : B (Td v) w = B (Td' v) w :=
    ((hT.swap_of_symmetric hSym) v w).trans (((hT'.swap_of_symmetric hSym) v w).symm)
  rw [hEq (U u) u,hU (Td u) u,hU (Td' u) u,hEq u (Ud u)]

end CalderonN
