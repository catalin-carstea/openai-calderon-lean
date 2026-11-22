module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-! Adapted from `SmoothClosedRangeLift` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

universe u

variable {P F G : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private def pushDerivative (L : F →ₗᵢ[ℝ] G) :
    (P →L[ℝ] F) →ₗᵢ[ℝ] (P →L[ℝ] G) where
  toLinearMap := (ContinuousLinearMap.compL ℝ P F G L.toContinuousLinearMap).toLinearMap
  norm_map' A := by
    change ‖L.toContinuousLinearMap.comp A‖ = ‖A‖
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro p
      simpa only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,L.norm_map]
        using A.le_opNorm p
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro p
      simpa only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,L.norm_map]
        using (L.toContinuousLinearMap.comp A).le_opNorm p

private theorem liftDerivative
    (L : F →ₗᵢ[ℝ] G) (hL : IsClosed (range L))
    (f : P → F) (x : P) {A : P →L[ℝ] G} (hA : HasFDerivAt (L ∘ f) A x) :
    ∃ B : P →L[ℝ] F, HasFDerivAt f B x ∧ pushDerivative L B = A := by
  have hRange (v : P) : A v ∈ range L := by
    have h := (hA.hasLineDerivAt (v := v)).tendsto_slope_zero_right
    apply hL.mem_of_tendsto h
    exact Eventually.of_forall fun r =>
      ⟨r⁻¹ • (f (x + r • v) - f x),by simp⟩
  let Ar := A.codRestrict L.toLinearMap.range hRange
  let B := (L.equivRange.symm.toContinuousLinearEquiv : _ →L[ℝ] F).comp Ar
  have hB (v : P) : L (B v) = A v := by
    have h := congrArg Subtype.val (L.equivRange.apply_symm_apply (Ar v))
    change L (B v) = A v at h
    exact h
  refine ⟨B,?_,ContinuousLinearMap.ext hB⟩
  rw [hasFDerivAt_iff_tendsto] at hA ⊢
  exact hA.congr (fun y => by
    congr 1
    rw [← L.norm_map, map_sub,map_sub,hB]
    simp only [Function.comp_apply,map_sub])

set_option maxHeartbeats 1200000 in
private theorem contDiffOn_nat_of_closedRangeLinearIsometry (n : ℕ) :
    ∀ {F G : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
      {V : Set P} (_hV : IsOpen V) (L : F →ₗᵢ[ℝ] G) (f : P → F),
        ContDiffOn ℝ n (L ∘ f) V → ContDiffOn ℝ n f V := by
  induction n with
  | zero =>
    intro F G _ _ _ _ _ V hV L f hf
    rw [Nat.cast_zero,contDiffOn_zero] at hf ⊢
    exact L.isometry.isEmbedding.continuousOn_iff.mpr hf
  | succ n ih =>
    intro F G _ _ _ _ _ V hV L f hf
    have hE := (contDiffOn_succ_iff_fderiv_of_isOpen hV).mp
      (show ContDiffOn ℝ ((n : ℕ∞ω)+1) (L ∘ f) V by exact_mod_cast hf)
    let D (x : P) := fderiv ℝ (L ∘ f) x
    have hL : IsClosed (range L) := L.isometry.isClosedEmbedding.isClosed_range
    have h (x : P) (hx : x ∈ V) : ∃ B : P →L[ℝ] F,
        HasFDerivAt f B x ∧ pushDerivative L B = D x :=
      liftDerivative L hL f x ((hE.1 x hx).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
    choose B hB hDB using h
    classical
    let b (x : P) : P →L[ℝ] F := if hx : x ∈ V then B x hx else 0
    have he : EqOn (pushDerivative L ∘ b) D V := fun x hx => by
      simpa only [Function.comp_def,b,dite_eq_left hx] using hDB x hx
    have hb : ContDiffOn ℝ n b V :=
      ih hV (pushDerivative L) b (hE.2.2.congr he)
    have hf' : ∀ x ∈ V, HasFDerivAt f (b x) x := fun x hx => by
      simpa only [b,dite_eq_left hx] using hB x hx
    have hFinal : ContDiffOn ℝ ((n : ℕ∞ω)+1) f V :=
      (contDiffOn_succ_iff_fderiv_of_isOpen hV).mpr
        ⟨fun x hx => (hf' x hx).differentiableAt.differentiableWithinAt,
          by simp, hb.congr (fun x hx => (hf' x hx).fderiv)⟩
    exact_mod_cast hFinal

/-- Smoothness of an open-parameter family in a Banach space can be tested
after a linear isometric inclusion into another normed space. -/
theorem contDiffOn_top_of_closedRangeLinearIsometry [CompleteSpace F]
    {V : Set P} (hV : IsOpen V) (L : F →ₗᵢ[ℝ] G) (f : P → F)
    (hf : ContDiffOn ℝ ∞ (L ∘ f) V) : ContDiffOn ℝ ∞ f V :=
  contDiffOn_infty.mpr fun n => contDiffOn_nat_of_closedRangeLinearIsometry n hV L f
    (hf.of_le (by simp))

end CalderonN
