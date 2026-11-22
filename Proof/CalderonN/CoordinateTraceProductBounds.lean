module

public import Proof.CalderonN.CoordinateTraceFirstTermBounds

import Mathlib.Tactic

/-! The product with the model adjoint correction uses the same
quadratic forms and does not require an angular commutator. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

private theorem product_first_base {R : Type*} [Ring R] (b D Z : R) :
    (b*D)*Z = (b*Z)*D+b*(D*Z-Z*D) := by noncomm_ring

theorem bounded_coordinate_product
    (H : CoordinateTraceFormContext hn Y) (U : CoordinateTraceDivergence hn Y)
    (Z : RegularTraceFiberFamily Y) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hD : ∀ i,PairedAdjoint H.Pairing (smoothSupportedTraceBaseDiff (axis i)) (U.baseAdjoint H.openSet i))
    (hLocal : ∀ x ∈ Y,∃ A : SmoothTraceSymbolAtoms hn,
      CoordinateTraceDivergenceBounds A H.openSet x (H.profile x) δ C U ∧
      SmoothTraceAngularBound hn 1 (C*H.profile x) (Z.1 x) ∧
      ∀ j,SmoothTraceAngularBound hn 1 (C*(H.profile x)^2) ((Z.derivative H.openSet (axis j)).1 x)) :
    H.Bound ((2*(dim:ℝ)^2+2*(dim:ℝ)+1)*(C*δ))
      (fun u => H.Pairing ((U.action H.openSet*Z.action H.openSet) u) u) := by
  let hY := H.openSet
  let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let B := H.Pairing
  let E := C*δ
  have hE := mul_nonneg hC hδ
  let a (i j : I dim) := (U.second i j).forward
  let b (i : I dim) := (U.first i).forward
  let c := U.zero.forward
  let dZ (i : I dim) := Z.derivative hY (axis i)
  have h₂ (i j : I dim) : H.Bound (E+E) (fun u =>
      B ((U.baseAdjoint hY i*(a i j).action hY*D j*Z.action hY) u) u) := by
    have h₁ := H.bound_left ((a i j).mul hY Z) (some j) (some i) 1 (by rfl) E hE (by
      intro x hx
      let β := H.profile x
      have hβ : 0 < β := H.profilePos x hx
      obtain ⟨A,hU,hZ,_⟩ := hLocal x hx
      refine ((hU.second i j).mul hZ (by positivity)).enlarge ?_
      change δ*(β⁻¹)^2*(C*β) ≤ E*β⁻¹
      apply le_of_eq
      dsimp only [E]
      field_simp)
    have h₂ := H.bound_left ((a i j).mul hY (dZ j)) none (some i) 2 (by rfl) E hE (by
      intro x hx
      let β := H.profile x
      have hβ : 0 < β := H.profilePos x hx
      obtain ⟨A,hU,_,hZ⟩ := hLocal x hx
      refine (((hU.second i j).mul (hZ j) (by positivity)).weaken (by positivity) (by decide : 1 ≤ 2)).enlarge ?_
      change δ*(β⁻¹)^2*(C*β^2) ≤ E*1
      apply le_of_eq
      dsimp only [E]
      field_simp)
    apply (h₁.add h₂).congr
    intro u
    have h := paired_product_divergence_form (B:=B) (D i) (U.baseAdjoint hY i) (D j)
      ((a i j).action hY) (Z.action hY) (smoothSupportedTracePairing_symm hn H.density) (hD i) u
    simpa only [traceCoordinateTest,RegularTraceFiberFamily.action_mul,RegularTraceFiberFamily.action_derivative,
      Module.End.mul_apply,b,dZ] using h.symm
  have h₁ (i : I dim) : H.Bound (E+E) (fun u => B (((b i).action hY*D i*Z.action hY) u) u) := by
    have h₁ := H.bound_left ((b i).mul hY Z) (some i) none 2 (by rfl) E hE (by
      intro x hx
      let β := H.profile x
      have hβ : 0 < β := H.profilePos x hx
      obtain ⟨A,hU,hZ,_⟩ := hLocal x hx
      refine ((hU.first i).symbol.angular.mul hZ (by positivity)).enlarge ?_
      change δ*β⁻¹*(C*β) ≤ E*1
      apply le_of_eq
      dsimp only [E]
      field_simp)
    have h₂ := H.bound_left ((b i).mul hY (dZ i)) none none 3 (by rfl) E hE (by
      intro x hx
      let β := H.profile x
      have hβ : 0 < β := H.profilePos x hx
      obtain ⟨A,hU,_,hZ⟩ := hLocal x hx
      refine (((hU.first i).symbol.angular.mul (hZ i) (by positivity)).weaken (by positivity) (by decide : 2 ≤ 3)).enlarge ?_
      change δ*β⁻¹*(C*β^2) ≤ E*β
      apply le_of_eq
      dsimp only [E]
      field_simp)
    apply (h₁.add h₂).congr
    intro u
    rw [product_first_base ((b i).action hY) (D i) (Z.action hY)]
    simp only [LinearMap.add_apply,map_add,traceCoordinateTest,RegularTraceFiberFamily.action_mul,
      RegularTraceFiberFamily.action_derivative,Module.End.mul_apply,dZ,D,B]
  have h₀ := H.bound_left (c.mul hY Z) none none 3 (by rfl) E hE (by
    intro x hx
    obtain ⟨A,hU,hZ,_⟩ := hLocal x hx
    refine (hU.zero.symbol.angular.mul hZ hδ).enlarge ?_
    change δ*(C*H.profile x) ≤ E*H.profile x
    apply le_of_eq
    dsimp only [E]
    ring)
  have hSum₂ := CoordinateTraceFormContext.Bound.sum Finset.univ
    (fun _ : I dim => ∑ _ : I dim,(E+E)) _ (fun i _ =>
      CoordinateTraceFormContext.Bound.sum Finset.univ (fun _ : I dim => E+E) _ (fun j _ => h₂ i j))
  have hSum₁ := CoordinateTraceFormContext.Bound.sum Finset.univ (fun _ : I dim => E+E) _ (fun i _ => h₁ i)
  refine (((hSum₂.add hSum₁).add h₀).congr ?_).enlarge ?_
  · intro u
    simp only [CoordinateTraceDivergence.action,CoordinateTraceDivergence.principal,c,a,b,D,B,hY,add_mul,
      RegularTraceFiberFamily.action_mul,traceCoordinateTest,Finset.sum_mul,LinearMap.add_apply,
      LinearMap.sum_apply,map_sum,map_add,Module.End.mul_apply]
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp only [E]
    apply le_of_eq
    ring

end CalderonN
