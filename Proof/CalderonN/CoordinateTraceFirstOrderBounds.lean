module

public import Proof.CalderonN.CoordinateTraceFirstOrderAdjoint
public import Proof.CalderonN.CoordinateTraceCoefficientBounds
public import Proof.CalderonN.SmoothTraceFiniteJetSums

import Proof.CalderonN.ActualConormalCoefficientBounds
import Mathlib.Tactic

/-! The adjoint of the first-order model has a lower angular order
term from differentiating its first coefficient. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

namespace CoordinateTraceFirstOrder

@[expose] def sub (P Q : CoordinateTraceFirstOrder Y) : CoordinateTraceFirstOrder Y :=
  ⟨fun i => (P.first i).sub (Q.first i),P.zero.sub Q.zero⟩

theorem skew_eq_paired_sub (U : CoordinateTraceDivergence hn Y) (hY : IsOpen Y) :
    U.skew hY = (ofPairedAdjoint hY U.density U.first U.zero).sub (ofPaired U.first U.zero) := by
  unfold CoordinateTraceDivergence.skew ofPairedAdjoint ofPaired sub
  congr 1
  apply Subtype.ext
  funext x
  simp only [CoordinateTraceDivergence.skewZeroSymbol,CoordinateTraceDivergence.skewZeroDerivative,
    adjointCorrection,RegularTraceFiberFamily.add,RegularTraceFiberFamily.sub]
  abel

end CoordinateTraceFirstOrder

namespace CoordinateTraceFirstOrderBounds

variable {A : SmoothTraceSymbolAtoms hn} {hY : IsOpen Y} {x : X dim} {β C D : ℝ}
variable {P Q : CoordinateTraceFirstOrder Y}

theorem enlarge (h : CoordinateTraceFirstOrderBounds A hY x β C P) (hβ : 0 ≤ β) (hCD : C ≤ D) :
    CoordinateTraceFirstOrderBounds A hY x β D P := by
  have h₁ := mul_le_mul_of_nonneg_right hCD hβ
  have h₂ := mul_le_mul_of_nonneg_right hCD (sq_nonneg β)
  refine ⟨fun i => (h.first i).enlarge hCD,fun i j => (h.firstDerivative i j).enlarge h₁,
    fun j => (h.zeroDerivative j).enlarge h₂,?_⟩
  obtain ⟨P₀,Q₀,he,hP,hQ⟩ := h.zeroParts
  exact ⟨P₀,Q₀,he,hP.enlarge h₁,hQ.enlarge h₁⟩

theorem neg (h : CoordinateTraceFirstOrderBounds A hY x β C P) (hx : x ∈ Y) :
    CoordinateTraceFirstOrderBounds A hY x β C P.neg := by
  refine ⟨fun i => (h.first i).neg,?_,?_,?_⟩
  · intro i j
    change SmoothTraceAngularBound hn 1 _ (((P.first i).neg.derivative hY (axis j)).1 x)
    rw [RegularTraceFiberFamily.derivative_neg_value hY _ _ hx]
    exact (h.firstDerivative i j).neg
  · intro j
    change SmoothTraceAngularBound hn 2 _ ((P.zero.neg.derivative hY (axis j)).1 x)
    rw [RegularTraceFiberFamily.derivative_neg_value hY _ _ hx]
    exact (h.zeroDerivative j).neg
  · obtain ⟨P₀,Q₀,he,hP,hQ⟩ := h.zeroParts
    refine ⟨-P₀,-Q₀,?_,hP.neg,hQ.neg⟩
    change -(P.zero.1 x) = -P₀+ -Q₀
    rw [he]
    abel

theorem sub (h : CoordinateTraceFirstOrderBounds A hY x β C P)
    (h' : CoordinateTraceFirstOrderBounds A hY x β D Q) (hx : x ∈ Y) :
    CoordinateTraceFirstOrderBounds A hY x β (C+D) (P.sub Q) := by
  refine ⟨fun i => (h.first i).sub (h'.first i),?_,?_,?_⟩
  · intro i j
    change SmoothTraceAngularBound hn 1 _ ((((P.first i).sub (Q.first i)).derivative hY (axis j)).1 x)
    rw [RegularTraceFiberFamily.derivative,RegularTraceFiberFamily.sub,Subtype.coe_mk,
      smoothSupportedTraceFiberDerivative_sub hY _ _ (P.first i).2 (Q.first i).2 _ hx,add_mul]
    exact (h.firstDerivative i j).sub (h'.firstDerivative i j)
  · intro j
    change SmoothTraceAngularBound hn 2 _ (((P.zero.sub Q.zero).derivative hY (axis j)).1 x)
    rw [RegularTraceFiberFamily.derivative,RegularTraceFiberFamily.sub,Subtype.coe_mk,
      smoothSupportedTraceFiberDerivative_sub hY _ _ P.zero.2 Q.zero.2 _ hx,add_mul]
    exact (h.zeroDerivative j).sub (h'.zeroDerivative j)
  · obtain ⟨P₀,P₁,hP,hP₀,hP₁⟩ := h.zeroParts
    obtain ⟨Q₀,Q₁,hQ,hQ₀,hQ₁⟩ := h'.zeroParts
    rw [add_mul]
    refine ⟨P₀-Q₀,P₁-Q₁,?_,hP₀.sub hQ₀,hP₁.sub hQ₁⟩
    change P.zero.1 x-Q.zero.1 x = _
    rw [hP,hQ]
    abel

end CoordinateTraceFirstOrderBounds

theorem coordinateTrace_pairedFirstOrder_bounds (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y) (x : X dim),x ∈ Y →
      ∀ β : ℝ,1 ≤ β →
      ∀ (P : I dim → PairedTraceFiberFamily hn Y) (Q : PairedTraceFiberFamily hn Y)
        (density : I dim → RegularTraceFiberFamily Y),
      (∀ i,PairedTraceFiberFamilyBounds A hY x β 2 1 C (P i)) →
      PairedTraceFiberFamilyBounds A hY x β 1 2 (C*β) Q →
      (∀ i,SmoothSupportedFiberJetBound hn hY x β 1 0 C (density i)) →
      CoordinateTraceFirstOrderBounds A hY x β D (CoordinateTraceFirstOrder.ofPaired P Q) ∧
      CoordinateTraceFirstOrderBounds A hY x β D (CoordinateTraceFirstOrder.ofPairedAdjoint hY density P Q) := by
  let E := (dim:ℝ)*(C+2*C*C)
  let D := C+E
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨D,add_nonneg hC hE,?_⟩
  intro A hY x hx β hβ P Q dens hP hQ hD
  have hβ₀ := zero_le_one.trans hβ
  have hAdj : SmoothSupportedFiberJetBound hn hY x β 1 1 (E*β)
      (CoordinateTraceFirstOrder.adjointCorrection hY dens P) := by
    have hF (i : I dim) : SmoothSupportedFiberJetBound hn hY x β 1 1 ((C+2*C*C)*β)
        (((P i).reverse.derivative hY (axis i)).add ((dens i).mul hY (P i).reverse)) := by
      have hA := (hP i).adj hx hβ₀
      have hP' := hA.jets.derivative (axis i) (norm_axis i).le
      have hM := (hD i).mul hx hβ₀ hC hC (hA.jets.restrict (by decide : 1 ≤ 2))
      refine (hP'.add hx hM).enlarge hβ₀ ?_
      have h := le_mul_of_one_le_right (show 0 ≤ 2*C*C by positivity) hβ
      simp only [pow_one]
      nlinarith only [h]
    have hTotal := SmoothSupportedFiberJetBound.finite_sum hx hβ₀ Finset.univ _ (fun _ => (C+2*C*C)*β)
      (fun i _ => hF i)
    simpa only [E,CoordinateTraceFirstOrder.adjointCorrection,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_assoc] using hTotal.neg hx
  have h₀ : CoordinateTraceFirstOrderBounds A hY x β C (CoordinateTraceFirstOrder.ofPaired P Q) := by
    refine ⟨fun i => (hP i).symbol,fun i j => (hP i).jets.atAxis (by decide) j,?_,?_⟩
    · intro i
      simpa only [CoordinateTraceFirstOrder.ofPaired,pow_two,mul_assoc] using hQ.jets.atAxis le_rfl i
    · exact ⟨Q.forward.1 x,0,(add_zero _).symm,hQ.symbol,smoothTraceAngularBound_zero hn 1 (mul_nonneg hC hβ₀)⟩
  refine ⟨h₀.enlarge hβ₀ (le_add_of_nonneg_right hE),?_⟩
  let T := CoordinateTraceFirstOrder.ofPairedAdjoint hY dens P Q
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    exact (hP i).adjSymbol.neg.enlarge (le_add_of_nonneg_right hE)
  · intro i j
    change SmoothTraceAngularBound hn 1 _ (((P i).reverse.neg.derivative hY (axis j)).1 x)
    rw [RegularTraceFiberFamily.derivative_neg_value hY _ _ hx]
    exact ((((hP i).adj hx hβ₀).jets.atAxis (by decide) j).neg).enlarge
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE) hβ₀)
  · intro i
    change SmoothTraceAngularBound hn 2 _
      (((Q.reverse.add (CoordinateTraceFirstOrder.adjointCorrection hY dens P)).derivative hY (axis i)).1 x)
    have h1 := (hQ.adj hx hβ₀).jets.atAxis le_rfl i
    have h2 := (hAdj.atAxis le_rfl i).weaken (by positivity) (by decide : 1 ≤ 2)
    rw [RegularTraceFiberFamily.derivative,RegularTraceFiberFamily.add,Subtype.coe_mk,
      smoothSupportedTraceFiberDerivative_add hY _ _ Q.reverse.2 (CoordinateTraceFirstOrder.adjointCorrection hY dens P).2 _ hx]
    simpa only [D,pow_two,add_mul,mul_assoc,PairedTraceFiberFamily.adj,RegularTraceFiberFamily.derivative] using h1.add h2
  · refine ⟨Q.reverse.1 x,(CoordinateTraceFirstOrder.adjointCorrection hY dens P).1 x,rfl,?_,?_⟩
    · exact hQ.adjSymbol.enlarge (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE) hβ₀)
    · exact hAdj.value.enlarge (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) hβ₀)

end CalderonN
