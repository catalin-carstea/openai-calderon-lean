module

public import Proof.CalderonN.CoordinateTraceCoefficientBounds
public import Proof.CalderonN.CoordinateTraceFormBounds

import Mathlib.Tactic

/-! The commutator with a single scalar divergence-form coefficient.
The symmetry step in its exact pairing puts only first derivatives
of the coefficients on the two test factors. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

theorem bounded_coordinate_comm_divergence
    (H : CoordinateTraceFormContext hn Y) (S Sd : CoordinateTraceFirstOrder Y)
    (U : CoordinateTraceDivergence hn Y) (i j : I dim) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hS : PairedAdjoint H.Pairing (S.action H.openSet) (Sd.action H.openSet))
    (hD : PairedAdjoint H.Pairing (smoothSupportedTraceBaseDiff (axis i)) (U.baseAdjoint H.openSet i))
    (ha : ∀ F : RegularTraceFiberFamily Y,
      F.action H.openSet*(U.second i j).forward.action H.openSet =
        (U.second i j).forward.action H.openSet*F.action H.openSet)
    (hLocal : ∀ x ∈ Y,∃ A : SmoothTraceSymbolAtoms hn,
      CoordinateTraceDivergenceBounds A H.openSet x (H.profile x) δ C U ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C S ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C Sd) :
    let A := U.baseAdjoint H.openSet i*(U.second i j).forward.action H.openSet*
      smoothSupportedTraceBaseDiff (axis j)
    H.Bound ((3*(dim:ℝ)+2)*(C*δ)) (fun u => H.Pairing ((S.action H.openSet*A-A*S.action H.openSet) u) u) := by
  dsimp only
  let hY := H.openSet
  let a := (U.second i j).forward
  let A := U.baseAdjoint hY i*a.action hY*smoothSupportedTraceBaseDiff (axis j)
  let B := H.Pairing
  let b := C*δ
  have hb : 0 ≤ b := mul_nonneg hC hδ
  let Di := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let Dj := smoothSupportedTraceBaseDiff (Y:=Y) (axis j)
  let F₁ (k : I dim) := (Sd.first k).derivative hY (axis i)
  let F₂ (k : I dim) := (S.first k).mul hY (a.derivative hY (axis k))
  let F₃ (k : I dim) := a.mul hY ((S.first k).derivative hY (axis j))
  let Q₁ := Sd.zero.derivative hY (axis i)
  let Q₂ := a.mul hY (S.zero.derivative hY (axis j))
  have h₁ (k : I dim) := H.bound_pair a (F₁ k) (some j) (some k) 2 0 1 (by rfl) (by rfl) b hb (by
    intro x hx
    let β := H.profile x
    have hβ : 0 < β := H.profilePos x hx
    obtain ⟨A,hU,_,hSd⟩ := hLocal x hx
    refine ⟨δ*(β⁻¹)^2,C*β,mul_nonneg hδ (sq_nonneg _),mul_nonneg hC hβ.le,
      hU.second i j,hSd.firstDerivative k i,?_⟩
    change δ*(β⁻¹)^2*(C*β) ≤ b*β⁻¹
    apply le_of_eq
    dsimp only [b]
    field_simp)
  have h₂ (k : I dim) := H.bound_left (F₂ k) (some j) (some i) 1 (by rfl) b hb (by
    intro x hx
    obtain ⟨A,hU,hS,_⟩ := hLocal x hx
    exact ((hS.first k).angular.mul (hU.secondDerivative i j k) hC).enlarge (by
      change C*(δ*(H.profile x)⁻¹) ≤ b*(H.profile x)⁻¹
      rw [mul_assoc]))
  have h₃ (k : I dim) := H.bound_left (F₃ k) (some k) (some i) 1 (by rfl) b hb (by
    intro x hx
    let β := H.profile x
    have hβ : 0 < β := H.profilePos x hx
    obtain ⟨A,hU,hS,_⟩ := hLocal x hx
    exact (hU.second i j |>.mul (hS.firstDerivative k j) (mul_nonneg hδ (sq_nonneg _))).enlarge (by
      change δ*(β⁻¹)^2*(C*β) ≤ b*β⁻¹
      apply le_of_eq
      dsimp only [b]
      field_simp))
  have h₄ := H.bound_pair a Q₁ (some j) none 2 0 2 (by rfl) (by rfl) b hb (by
    intro x hx
    let β := H.profile x
    have hβ : 0 < β := H.profilePos x hx
    obtain ⟨A,hU,_,hSd⟩ := hLocal x hx
    refine ⟨δ*(β⁻¹)^2,C*β^2,mul_nonneg hδ (sq_nonneg _),mul_nonneg hC (sq_nonneg _),
      hU.second i j,hSd.zeroDerivative i,?_⟩
    change δ*(β⁻¹)^2*(C*β^2) ≤ b*1
    apply le_of_eq
    dsimp only [b]
    field_simp)
  have h₅ := H.bound_left Q₂ none (some i) 2 (by rfl) b hb (by
    intro x hx
    let β := H.profile x
    have hβ : 0 < β := H.profilePos x hx
    obtain ⟨A,hU,hS,_⟩ := hLocal x hx
    exact (hU.second i j |>.mul (hS.zeroDerivative j) (mul_nonneg hδ (sq_nonneg _))).enlarge (by
      change δ*(β⁻¹)^2*(C*β^2) ≤ b*1
      apply le_of_eq
      dsimp only [b]
      field_simp))
  have hs := CoordinateTraceFormContext.Bound.sum Finset.univ (fun _ : I dim => b+b+b) _
    (fun k _ => ((h₁ k).add (h₂ k)).sub (h₃ k))
  refine (((hs.add h₄).sub h₅).congr ?_).enlarge ?_
  · intro u
    have h := paired_coordinate_comm_divergence B hY S Sd a (U.baseAdjoint hY i) i j u
      (smoothSupportedTracePairing_symm hn H.density) hS hD ha
    simpa only [coordinateCoefficientPair,traceCoordinateTest,CoordinateTraceFormContext.oneAction,Module.End.one_apply,F₁,F₂,F₃,Q₁,Q₂] using h.symm
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp only [b]
    apply le_of_eq
    ring

end CalderonN
