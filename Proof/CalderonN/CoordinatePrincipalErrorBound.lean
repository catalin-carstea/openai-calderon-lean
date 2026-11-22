module

public import Proof.CalderonN.CoordinateTraceProductBounds

import Mathlib.Tactic

/-! Combine the integrated commutator and product estimates in the
principal adjoint error form. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

private def commutatorTestLinear (B : SmoothSupportedTraceSection Y →ₗ[ℝ] SmoothSupportedTraceSection Y →ₗ[ℝ] ℝ)
    (S : Module.End ℝ (SmoothSupportedTraceSection Y)) (u : SmoothSupportedTraceSection Y) :
    Module.End ℝ (SmoothSupportedTraceSection Y) →ₗ[ℝ] ℝ where
  toFun A := B ((S*A-A*S) u) u
  map_add' A D := by
    simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,map_add,map_sub]
    ring
  map_smul' a A := by
    simp only [LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,map_smul,map_sub,
      RingHom.id_apply,smul_eq_mul]
    ring

@[expose] def coordinatePrincipalCommConstant (dim : ℕ) (C : ℝ) : ℝ :=
  (dim:ℝ)^2*(3*(dim:ℝ)+2)+(dim:ℝ)*((dim:ℝ)*(7+C)+4)+2*(dim:ℝ)+3

theorem bounded_coordinate_commutator
    (H : CoordinateTraceFormContext hn Y) (S Sd : CoordinateTraceFirstOrder Y)
    (U : CoordinateTraceDivergence hn Y) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hFloor : ∀ x ∈ Y,1 ≤ H.profile x)
    (hS : PairedAdjoint H.Pairing (S.action H.openSet) (Sd.action H.openSet))
    (hD : ∀ i,PairedAdjoint H.Pairing (smoothSupportedTraceBaseDiff (axis i)) (U.baseAdjoint H.openSet i))
    (ha : ∀ i j (F : RegularTraceFiberFamily Y),
      F.action H.openSet*(U.second i j).forward.action H.openSet =
        (U.second i j).forward.action H.openSet*F.action H.openSet)
    (hLocal : ∀ x ∈ Y,∃ A : SmoothTraceSymbolAtoms hn,
      CoordinateTraceDivergenceBounds A H.openSet x (H.profile x) δ C U ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C S ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C Sd) :
    H.Bound (coordinatePrincipalCommConstant dim C*(C*δ))
      (fun u => H.Pairing ((S.action H.openSet*U.action H.openSet-U.action H.openSet*S.action H.openSet) u) u) := by
  let hY := H.openSet
  let E₂ := (3*(dim:ℝ)+2)*(C*δ)
  let E₁ := ((dim:ℝ)*(7+C)+4)*(C*δ)
  let h₂ (i j : I dim) := bounded_coordinate_comm_divergence H S Sd U i j C δ hC hδ hS (hD i) (ha i j) hLocal
  have hLocal' (x : X dim) (hx : x ∈ Y) :
      ∃ A : SmoothTraceSymbolAtoms hn,
        CoordinateTraceDivergenceBounds A H.openSet x (H.profile x) δ C U ∧
        CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C S := by
    obtain ⟨A,hU,hS,_⟩ := hLocal x hx
    exact ⟨A,hU,hS⟩
  let h₁ (i : I dim) := bounded_coordinate_comm_first H S U i C δ hC hδ hFloor hD hLocal'
  let h₀ := bounded_coordinate_comm_zero H S U C δ hC hδ hLocal'
  have hSum₂ := CoordinateTraceFormContext.Bound.sum Finset.univ (fun _ : I dim => ∑ _ : I dim,E₂) _ (fun i _ =>
    CoordinateTraceFormContext.Bound.sum Finset.univ (fun _ : I dim => E₂) _ (fun j _ => h₂ i j))
  have hSum₁ := CoordinateTraceFormContext.Bound.sum Finset.univ (fun _ : I dim => E₁) _ (fun i _ => h₁ i)
  refine (((hSum₂.add hSum₁).add h₀).congr ?_).enlarge ?_
  · intro u
    let L := commutatorTestLinear H.Pairing (S.action hY) u
    change (∑ i,∑ j,L (U.baseAdjoint hY i*(U.second i j).forward.action hY*smoothSupportedTraceBaseDiff (axis j)))+
      (∑ i,L ((U.first i).forward.action hY*smoothSupportedTraceBaseDiff (axis i)))+L (U.zero.forward.action hY) =
        L (U.action hY)
    simp only [CoordinateTraceDivergence.action,CoordinateTraceDivergence.principal,map_add,map_sum]
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,E₁,E₂,coordinatePrincipalCommConstant]
    apply le_of_eq
    ring

theorem bounded_coordinate_principalAdjointError
    (H : CoordinateTraceFormContext hn Y) (T Td Vd : CoordinateTraceFirstOrder Y)
    (U : CoordinateTraceDivergence hn Y) (Z : RegularTraceFiberFamily Y) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hFloor : ∀ x ∈ Y,1 ≤ H.profile x)
    (hT : PairedAdjoint H.Pairing (T.action H.openSet) (Td.action H.openSet))
    (hD : ∀ i,PairedAdjoint H.Pairing (smoothSupportedTraceBaseDiff (axis i)) (U.baseAdjoint H.openSet i))
    (hA : ∀ i j,(U.second i j).reverse.action H.openSet = (U.second j i).forward.action H.openSet)
    (ha : ∀ i j (F : RegularTraceFiberFamily Y),
      F.action H.openSet*(U.second i j).forward.action H.openSet =
        (U.second i j).forward.action H.openSet*F.action H.openSet)
    (hVd : Vd.action H.openSet = -(U.skew H.openSet).action H.openSet)
    (hLocal : ∀ x ∈ Y,∃ A : SmoothTraceSymbolAtoms hn,
      CoordinateTraceDivergenceBounds A H.openSet x (H.profile x) δ C U ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C T ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C Td ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C (U.skew H.openSet) ∧
      CoordinateTraceFirstOrderBounds A H.openSet x (H.profile x) C Vd ∧
      SmoothTraceAngularBound hn 1 (C*H.profile x) (Z.1 x) ∧
      ∀ j,SmoothTraceAngularBound hn 1 (C*(H.profile x)^2) ((Z.derivative H.openSet (axis j)).1 x)) :
    let hY := H.openSet
    let L := Td.action hY+Z.action hY
    let Λ := 5*coordinatePrincipalCommConstant dim C+4*(2*(dim:ℝ)^2+2*(dim:ℝ)+1)
    H.Bound (Λ*(C*δ))
      (movingTraceAdjointErrorForm H.Pairing (T.action hY) (Td.action hY) L (U.action hY) (U.adjointAction hY)) := by
  dsimp only
  let hY := H.openSet
  let B := H.Pairing
  have hSym : ∀ u v,B u v = B v u := smoothSupportedTracePairing_symm hn H.density
  have hU := U.paired hY H.density H.densitySmooth hD hA
  have hV : PairedAdjoint H.Pairing ((U.skew hY).action hY) (Vd.action hY) := by
    rw [hVd,← U.adjointAction_sub_action hY]
    have he : -(U.adjointAction hY-U.action hY) = U.action hY-U.adjointAction hY := by abel
    rw [he]
    exact (hU.swap_of_symmetric hSym).sub hU
  have h₁ := bounded_coordinate_commutator H Td T U C δ hC hδ hFloor (hT.swap_of_symmetric hSym) hD ha (by
    intro x hx
    obtain ⟨A,hU,hT,hTd,_,_,_,_⟩ := hLocal x hx
    exact ⟨A,hU,hTd,hT⟩)
  have h₂ := bounded_coordinate_commutator H (U.skew hY) Vd U C δ hC hδ hFloor hV hD ha (by
    intro x hx
    obtain ⟨A,hU,_,_,hV,hVd,_,_⟩ := hLocal x hx
    exact ⟨A,hU,hV,hVd⟩)
  have h₃ := bounded_coordinate_product H U Z C δ hC hδ hD (by
    intro x hx
    obtain ⟨A,hU,_,_,_,_,hZ,hZ'⟩ := hLocal x hx
    exact ⟨A,hU,hZ,hZ'⟩)
  refine ((((h₁.const_mul 4).add h₂).sub (h₃.const_mul 4)).congr ?_).enlarge ?_
  · intro u
    rw [paired_movingTraceAdjointErrorForm_reduce _ _ _ _ _ _ hSym hT hU,
      U.adjointAction_sub_action hY]
    have hh : Td.action hY+Z.action hY-Td.action hY = Z.action hY := by abel
    rw [hh]
  · rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    apply le_of_eq
    ring

end CalderonN
