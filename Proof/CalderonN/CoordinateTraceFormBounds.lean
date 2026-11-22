module

public import Proof.CalderonN.CoordinateTraceCommutatorForms
public import Proof.CalderonN.PairedTraceFiberFamilyBounds

import Proof.CalderonN.ActualConormalCoefficientBounds
import Mathlib.Tactic

/-! The physical quadrature is fixed throughout the sum of coordinate
pairings. Each summand uses the same test energy majorant. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

structure CoordinateTraceFormContext (hn : 3 ≤ dim) (Y : Set (X dim)) where
  openSet : IsOpen Y
  density : X dim → ℝ
  profile : X dim → ℝ
  densitySmooth : ContDiffOn ℝ ∞ density Y
  densityNonneg : ∀ x ∈ Y,0 ≤ density x
  profilePos : ∀ x ∈ Y,0 < profile x

namespace CoordinateTraceFormContext

variable {hn : 3 ≤ dim}

abbrev Pairing (H : CoordinateTraceFormContext hn Y) :=
  smoothSupportedTracePairingL hn H.openSet H.density H.densitySmooth

@[expose] def Bound (H : CoordinateTraceFormContext hn Y) (C : ℝ)
    (q : SmoothSupportedTraceSection Y → ℝ) : Prop :=
  ∀ u e,IntegrableOn e Y →
    (∀ x ∈ Y,H.density x*coordinateTraceEnergy hn H.profile u x ≤ e x) →
    |q u| ≤ C*(∫ x in Y,e x)

variable {H : CoordinateTraceFormContext hn Y} {C D : ℝ}
variable {q p : SmoothSupportedTraceSection Y → ℝ}

theorem Bound.add (h : H.Bound C q) (h' : H.Bound D p) :
    H.Bound (C+D) (fun u => q u+p u) := by
  intro u e he hm
  exact ((abs_add_le _ _).trans (add_le_add (h u e he hm) (h' u e he hm))).trans_eq (by rw [add_mul])

theorem Bound.sub (h : H.Bound C q) (h' : H.Bound D p) :
    H.Bound (C+D) (fun u => q u-p u) := by
  intro u e he hm
  have hh : |q u-p u| ≤ |q u|+|p u| := by rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
  exact (hh.trans (add_le_add (h u e he hm) (h' u e he hm))).trans_eq (by rw [add_mul])

theorem Bound.neg (h : H.Bound C q) : H.Bound C (fun u => -q u) := by
  intro u e he hm
  rw [abs_neg]
  exact h u e he hm

theorem Bound.enlarge (h : H.Bound C q) (hCD : C ≤ D) : H.Bound D q := by
  intro u e he hm
  refine (h u e he hm).trans (mul_le_mul_of_nonneg_right hCD ?_)
  apply setIntegral_nonneg H.openSet.measurableSet
  intro x hx
  have h := H.profilePos x hx
  have he : 0 ≤ coordinateTraceEnergy hn H.profile u x := by unfold coordinateTraceEnergy; positivity
  exact (mul_nonneg (H.densityNonneg x hx) he).trans (hm x hx)

theorem Bound.sum {ι : Type*} (s : Finset ι) (C : ι → ℝ) (f : ι → SmoothSupportedTraceSection Y → ℝ)
    (h : ∀ i ∈ s,H.Bound (C i) (f i)) :
    H.Bound (∑ i ∈ s,C i) (fun u => ∑ i ∈ s,f i u) := by
  intro u e he hm
  exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi => h i hi u e he hm))).trans_eq
    (by rw [Finset.sum_mul])

theorem Bound.congr (h : H.Bound C q) (he : ∀ u,q u = p u) : H.Bound C p :=
  fun u e hE hm => he u ▸ h u e hE hm

theorem Bound.const_mul (h : H.Bound C q) (a : ℝ) :
    H.Bound (|a| * C) (fun u => a*q u) := by
  intro u e he hm
  rw [abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (h u e he hm) (abs_nonneg _)

theorem bound_pair (H : CoordinateTraceFormContext hn Y)
    (F G : RegularTraceFiberFamily Y) (i j : Option (I dim)) (a : Fin 4)
    (k l : ℕ) (hi : (traceCoordinateTestOrder i).val = a.val+k)
    (hj : (traceCoordinateTestOrder j).val = a.rev.val+l) (C : ℝ) (hC : 0 ≤ C)
    (hBounds : ∀ x ∈ Y,∃ D E : ℝ,0 ≤ D ∧ 0 ≤ E ∧
      SmoothTraceAngularBound hn k D (F.1 x) ∧ SmoothTraceAngularBound hn l E (G.1 x) ∧
      D*E ≤ C*traceCoordinatePairWeight (H.profile x) i j) :
    H.Bound C (coordinateCoefficientPair H.Pairing H.openSet F G i j) :=
  fun u e he hm => abs_supported_coordinateTrace_pair_le hn H.openSet H.density H.profile e
    H.densitySmooth H.densityNonneg H.profilePos he u hm F G i j a k l hi hj C hC hBounds

theorem oneAction (hY : IsOpen Y) :
    (RegularTraceFiberFamily.scalar (Y:=Y) hY (fun _ => 1) contDiffOn_const).action hY = 1 := by
  ext w : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [RegularTraceFiberFamily.action_fiber,RegularTraceFiberFamily.scalar,one_smul,Module.End.one_apply]

theorem bound_left (H : CoordinateTraceFormContext hn Y) (F : RegularTraceFiberFamily Y)
    (i j : Option (I dim)) (k : ℕ) (hOrder : (traceCoordinateTestOrder i).val =
      (traceCoordinateTestOrder j).rev.val+k) (C : ℝ) (hC : 0 ≤ C)
    (hBounds : ∀ x ∈ Y,SmoothTraceAngularBound hn k
      (C*traceCoordinatePairWeight (H.profile x) i j) (F.1 x)) :
    H.Bound C (fun u => H.Pairing (F.action H.openSet (traceCoordinateTest u i)) (traceCoordinateTest u j)) := by
  let I₀ := RegularTraceFiberFamily.scalar H.openSet (fun _ => 1) contDiffOn_const
  have h := H.bound_pair F I₀ i j (traceCoordinateTestOrder j).rev k 0 hOrder
    (by rw [Fin.rev_rev,Nat.add_zero]) C hC (by
      intro x hx
      have hβ := H.profilePos x hx
      have hW : 0 ≤ traceCoordinatePairWeight (H.profile x) i j := by
        cases i <;> cases j <;> dsimp only [traceCoordinatePairWeight] <;> positivity
      refine ⟨_,1,mul_nonneg hC hW,zero_le_one,hBounds x hx,?_,by rw [mul_one]⟩
      simpa only [I₀,RegularTraceFiberFamily.scalar,one_smul] using
        (smoothTraceIdentity_commutatorBounds hn 0).bound)
  apply h.congr
  intro u
  simp only [coordinateCoefficientPair,I₀,oneAction,Module.End.one_apply]

end CoordinateTraceFormContext

end CalderonN
