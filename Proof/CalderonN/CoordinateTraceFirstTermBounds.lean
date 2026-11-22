module

public import Proof.CalderonN.CoordinateTraceDivergenceTermBound

import Mathlib.Tactic

/-! First-order and multiplication terms of the principal commutator. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

theorem bounded_coordinate_comm_first
    (H : CoordinateTraceFormContext hn Y) (S : CoordinateTraceFirstOrder Y)
    (U : CoordinateTraceDivergence hn Y) (j : I dim) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hFloor : ∀ x ∈ Y,1 ≤ H.profile x)
    (hD : ∀ i,PairedAdjoint H.Pairing (smoothSupportedTraceBaseDiff (axis i)) (U.baseAdjoint H.openSet i))
    (hLocal : ∀ x ∈ Y,∃ A : SmoothTraceSymbolAtoms hn,
      CoordinateTraceDivergenceBounds A H.openSet x (H.profile x) δ C U ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C S) :
    let A := (U.first j).forward.action H.openSet*smoothSupportedTraceBaseDiff (axis j)
    H.Bound (((dim:ℝ)*(7+C)+4)*(C*δ))
      (fun u => H.Pairing ((S.action H.openSet*A-A*S.action H.openSet) u) u) := by
  dsimp only
  let hY := H.openSet
  let b := (U.first j).forward
  let B := H.Pairing
  let E := C*δ
  have hE : 0 ≤ E := mul_nonneg hC hδ
  let F₁ (k : I dim) := (S.first k).comm hY b
  let F₂ (k : I dim) := ((S.first k).mul hY (b.derivative hY (axis k))).sub
    (((F₁ k).derivative hY (axis k)).add ((U.density k).mul hY (F₁ k)))
  let F₃ (k : I dim) := b.mul hY ((S.first k).derivative hY (axis j))
  let Q₁ := S.zero.comm hY b
  let Q₂ := b.mul hY (S.zero.derivative hY (axis j))
  have h₁ (k : I dim) := H.bound_left (F₁ k) (some j) (some k) 1 (by rfl) E hE (by
    intro x hx
    obtain ⟨A,hU,hS⟩ := hLocal x hx
    have h := ((hS.first k).comm (hU.first j).symbol).angular (by decide : 0 < 1+1)
    exact h.enlarge (by change C*(δ*(H.profile x)⁻¹) ≤ E*(H.profile x)⁻¹; rw [mul_assoc]))
  have h₂ (k : I dim) := H.bound_left (F₂ k) (some j) none 2 (by rfl) ((5+C)*E) (by positivity) (by
    intro x hx
    let β := H.profile x
    have hβ : 0 < β := H.profilePos x hx
    obtain ⟨A,hU,hS⟩ := hLocal x hx
    have hInv : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ.le
    have hb : 0 ≤ δ*β⁻¹ := mul_nonneg hδ hInv
    have hp := (hS.first k).angular
    have hbp := (hU.first j).symbol.angular
    have hdb : SmoothTraceAngularBound hn 1 δ ((b.derivative hY (axis k)).1 x) := by
      refine ((hU.first j).jets.atAxis (by decide) k).enlarge ?_
      change δ*β⁻¹*β ≤ δ
      rw [mul_assoc,inv_mul_cancel₀ hβ.ne',mul_one]
    have hdp := hS.firstDerivative k k
    have hdP := hp.mul hdb hC
    have hdC : SmoothTraceAngularBound hn 2 (4*E) (((F₁ k).derivative hY (axis k)).1 x) := by
      simp only [F₁,RegularTraceFiberFamily.comm,RegularTraceFiberFamily.derivative,RegularTraceFiberFamily.mul,
        RegularTraceFiberFamily.sub]
      rw [smoothSupportedTraceFiberDerivative_sub hY _ _ ((S.first k).2.mul hY b.2)
          (b.2.mul hY (S.first k).2) (axis k) hx,
        smoothSupportedTraceFiberDerivative_mul hY _ _ (S.first k).2 b.2 (axis k) hx,
        smoothSupportedTraceFiberDerivative_mul hY _ _ b.2 (S.first k).2 (axis k) hx]
      have hL := hdp.mul hbp (mul_nonneg hC hβ.le)
      have hR := hdb.mul hp hδ
      have hS' := hbp.mul hdp hb
      refine ((hL.add hdP).sub (hR.add hS')).enlarge ?_
      change C*β*(δ*β⁻¹)+C*δ+(δ*C+δ*β⁻¹*(C*β)) ≤ 4*E
      apply le_of_eq
      dsimp only [E]
      field_simp <;> ring
    have hComm := ((hS.first k).comm (hU.first j).symbol).angular (by decide : 0 < 1+1)
    have hdc := (hU.density k).mul hComm hC
    have hdcm : SmoothTraceAngularBound hn 2 (C*E) (((U.density k).mul hY (F₁ k)).1 x) := by
      refine (hdc.weaken (by positivity) (by decide : 1 ≤ 2)).enlarge ?_
      change C*(C*(δ*β⁻¹)) ≤ C*E
      have hB : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hFloor x hx)
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hδ) hC) hC).trans_eq
        (by dsimp only [E]; ring)
    refine (hdP.sub (hdC.add hdcm)).enlarge ?_
    change C*δ+(4*E+C*E) ≤ (5+C)*E*1
    apply le_of_eq
    dsimp only [E]
    ring)
  have h₃ (k : I dim) := H.bound_left (F₃ k) (some k) none 2 (by rfl) E hE (by
    intro x hx
    let β := H.profile x
    have hβ : 0 < β := H.profilePos x hx
    obtain ⟨A,hU,hS⟩ := hLocal x hx
    refine ((hU.first j).symbol.angular.mul (hS.firstDerivative k j) (by positivity)).enlarge ?_
    change δ*β⁻¹*(C*β) ≤ E*1
    apply le_of_eq
    dsimp only [E]
    field_simp)
  have h₄ := H.bound_left Q₁ (some j) none 2 (by rfl) (3*E) (by positivity) (by
    intro x hx
    let β := H.profile x
    have hβ : 0 < β := H.profilePos x hx
    obtain ⟨A,hU,hS⟩ := hLocal x hx
    refine (hS.zero_comm hβ.le (hU.first j).symbol).enlarge ?_
    change 3*(C*β*(δ*β⁻¹)) ≤ (3*E)*1
    apply le_of_eq
    dsimp only [E]
    field_simp)
  have h₅ := H.bound_left Q₂ none none 3 (by rfl) E hE (by
    intro x hx
    let β := H.profile x
    have hβ : 0 < β := H.profilePos x hx
    obtain ⟨A,hU,hS⟩ := hLocal x hx
    refine ((hU.first j).symbol.angular.mul (hS.zeroDerivative j) (by positivity)).enlarge ?_
    change δ*β⁻¹*(C*β^2) ≤ E*β
    apply le_of_eq
    dsimp only [E]
    field_simp)
  have hs := CoordinateTraceFormContext.Bound.sum Finset.univ (fun _ : I dim => E+(5+C)*E+E) _
    (fun k _ => (((h₁ k).neg).add (h₂ k)).sub (h₃ k))
  refine (((hs.add h₄).sub h₅).congr ?_).enlarge ?_
  · intro u
    exact (paired_coordinate_comm_first B hY S b U.density (U.baseAdjoint hY) j u
      (smoothSupportedTracePairing_symm hn H.density) hD (fun _ => rfl)).symm
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp only [E]
    apply le_of_eq
    ring

theorem bounded_coordinate_comm_zero
    (H : CoordinateTraceFormContext hn Y) (S : CoordinateTraceFirstOrder Y)
    (U : CoordinateTraceDivergence hn Y) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hLocal : ∀ x ∈ Y,∃ A : SmoothTraceSymbolAtoms hn,
      CoordinateTraceDivergenceBounds A H.openSet x (H.profile x) δ C U ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C S) :
    let A := U.zero.forward.action H.openSet
    H.Bound ((2*(dim:ℝ)+3)*(C*δ))
      (fun u => H.Pairing ((S.action H.openSet*A-A*S.action H.openSet) u) u) := by
  dsimp only
  let hY := H.openSet
  let c := U.zero.forward
  let B := H.Pairing
  let E := C*δ
  have hE := mul_nonneg hC hδ
  let F (k : I dim) := (S.first k).comm hY c
  let G (k : I dim) := (S.first k).mul hY (c.derivative hY (axis k))
  have hF (k : I dim) := H.bound_left (F k) (some k) none 2 (by rfl) E hE (by
    intro x hx
    obtain ⟨A,hU,hS⟩ := hLocal x hx
    exact (((hS.first k).comm hU.zero.symbol).angular (by decide : 0 < 1+2)).enlarge
      (by change C*δ ≤ E*1; rw [mul_one]))
  have hG (k : I dim) := H.bound_left (G k) none none 3 (by rfl) E hE (by
    intro x hx
    obtain ⟨A,hU,hS⟩ := hLocal x hx
    exact ((hS.first k).angular.mul (hU.zero.jets.atAxis le_rfl k) hC).enlarge
      (by change C*(δ*H.profile x) ≤ E*H.profile x; rw [mul_assoc]))
  have hQ := H.bound_left (S.zero.comm hY c) none none 3 (by rfl) (3*E) (by positivity) (by
    intro x hx
    obtain ⟨A,hU,hS⟩ := hLocal x hx
    exact (hS.zero_comm (H.profilePos x hx).le hU.zero.symbol).enlarge (by
      change 3*(C*H.profile x*δ) ≤ (3*E)*H.profile x
      apply le_of_eq
      dsimp only [E]
      ring))
  have hs := CoordinateTraceFormContext.Bound.sum Finset.univ (fun _ : I dim => E+E) _
    (fun k _ => (hF k).add (hG k))
  refine ((hs.add hQ).congr ?_).enlarge ?_
  · intro u
    exact (paired_coordinate_comm_zero B hY S c u).symm
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp only [E]
    apply le_of_eq
    ring

end CalderonN
