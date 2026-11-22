module

public import Proof.CalderonN.ClosedBallJetEvaluation
public import Mathlib.Analysis.Normed.Operator.NormedSpace

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic

/-! Adapted from `ClosedBallJetSmooth` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Classical

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

local instance (priority := 1500) ballJetCLMNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) : NormedAddCommGroup (E →L[ℝ] (BallJet dim) k) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance (priority := 1500) ballJetCLMNormedSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (k : ℕ) : NormedSpace ℝ (E →L[ℝ] (BallJet dim) k) :=
  ContinuousLinearMap.toNormedSpace

private theorem norm_taylorRemainder_of_second_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : Set E} (hD : Convex ℝ D) {f : E → F} (hf : ContDiff ℝ ∞ f)
    {M : ℝ} (hM : 0 ≤ M)
    (hBound : ∀ z ∈ D, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    ‖f y - f x - (fderiv ℝ f x) (y-x)‖ ≤ M * ‖y-x‖^2 := by
  let A := fderiv ℝ f x
  let g (z : E) := f z - A (z-x)
  have hF := hf.fderiv_right (m := ∞) (by simp)
  have hS : segment ℝ x y ⊆ D := hD.segment_subset hx hy
  have hGrad (z : E) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ f z - A‖ ≤ M * ‖y-x‖ :=
    (Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hF.differentiable (by simp) z) hBound hD hx (hS hz)).trans
        (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hM)
  have hg (z : E) : HasFDerivAt g (fderiv ℝ f z - A) z := by
    have hA : HasFDerivAt (fun w => A (w-x)) A z := by
      simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using
        A.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)
    have hg' := (hf.differentiable (by simp) z).hasFDerivAt.sub hA
    exact hg'
  have hRes := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hg z).hasFDerivWithinAt) hGrad (convex_segment x y)
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  change ‖f y - A (y-x) - (f x - A (x-x))‖ ≤ _ at hRes
  rw [sub_self,map_zero,sub_zero,sub_right_comm] at hRes
  exact hRes.trans_eq (by ring)

abbrev ClosedBallEval (dim : ℕ) [NeZero dim] (k m : ℕ) := (ClosedBallSobolev dim) m →L[ℝ] (BallJet dim) k

/-- Operator-norm evaluation, with the values outside the closed ball
unused. -/
@[expose] def closedBallEval (dim : ℕ) [NeZero dim] (k m : ℕ) (z : (X dim)) : (ClosedBallEval dim) k m :=
  if hz : z ∈ closedBall (0 : (X dim)) 1
    then (ContinuousMap.evalCLM ℝ (⟨z,hz⟩ : (UnitClosedBall dim))).comp ((closedBallJetL dim) k m)
    else 0

theorem closedBallEval_apply (k m : ℕ) (u : (ClosedBallSobolev dim) m) (z : (UnitClosedBall dim)) :
    (closedBallEval dim) k m z u = (closedBallJetL dim) k m u z := by
  rw [closedBallEval,dite_eq_left z.property]
  rfl

set_option maxHeartbeats 1500000 in
@[expose] def closedBallEvalCurryL (dim : ℕ) [NeZero dim] (k m : ℕ) :
    (ClosedBallEval dim) (k+1) m →L[ℝ] (X dim) →L[ℝ] (ClosedBallEval dim) k m :=
  let E := (ClosedBallSobolev dim) m
  let A := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => (X dim)) ℝ).toContinuousLinearEquiv
  ((ContinuousLinearMap.flipₗᵢ ℝ E (X dim) ((BallJet dim) k)).toContinuousLinearEquiv :
      (E →L[ℝ] (X dim) →L[ℝ] (BallJet dim) k) →L[ℝ] ((X dim) →L[ℝ] E →L[ℝ] (BallJet dim) k)).comp
    (ContinuousLinearMap.compL ℝ E ((BallJet dim) (k+1)) ((X dim) →L[ℝ] (BallJet dim) k)
      (A : (BallJet dim) (k+1) →L[ℝ] (X dim) →L[ℝ] (BallJet dim) k))

private theorem closedBallEvalCurryL_apply (k m : ℕ) (J : (ClosedBallEval dim) (k+1) m)
    (v : (X dim)) (u : (ClosedBallSobolev dim) m) :
    (closedBallEvalCurryL dim) k m J v u = (J u).curryLeft v := rfl

set_option maxHeartbeats 1400000 in
private theorem closedBallEval_taylor_pointwise (k m : ℕ) (hm : k+dim+3 ≤ m)
    (x y : (UnitClosedBall dim)) (u : (ClosedBallSobolev dim) m) :
    ‖(closedBallEval dim) k m y u - (closedBallEval dim) k m x u -
      ((closedBallEval dim) (k+1) m x u).curryLeft ((y:(X dim))-(x:(X dim)))‖ ≤
      ((ballJetEmbeddingConstant dim) * ‖u‖) * ‖(y:(X dim))-(x:(X dim))‖^2 := by
  let J (j : ℕ) (z : (UnitClosedBall dim)) : (ClosedBallEval dim) j m := (closedBallEval dim) j m z
  let L : (ClosedBallSobolev dim) m →L[ℝ] (BallJet dim) k :=
    J k y - J k x - (closedBallEvalCurryL dim) k m (J (k+1) x) ((y:(X dim))-(x:(X dim)))
  have hClosed : IsClosed {v : (ClosedBallSobolev dim) m |
      ‖L v‖ ≤ ((ballJetEmbeddingConstant dim) * ‖v‖) * ‖(y:(X dim))-(x:(X dim))‖^2} :=
    isClosed_le L.continuous.norm ((continuous_const.mul continuous_norm).mul continuous_const)
  have hExpr (v : (ClosedBallSobolev dim) m) :
      L v = J k y v - J k x v - (J (k+1) x v).curryLeft ((y:(X dim))-(x:(X dim))) := by
    simp only [L,sub_apply,closedBallEvalCurryL_apply]
  have hMem : ∀ v ∈ Set.range ((denseSmoothBallSobolev dim) m),
      ‖L v‖ ≤ ((ballJetEmbeddingConstant dim) * ‖v‖) * ‖(y:(X dim))-(x:(X dim))‖^2 := by
    rintro v ⟨b,rfl⟩
    rw [hExpr]
    have hJ (j : ℕ) (hj : j+dim+1 ≤ m) (z : (UnitClosedBall dim)) :
        J j z ((denseSmoothBallSobolev dim) m b) = iteratedFDeriv ℝ j b.1 z := by
      dsimp only [J]
      rw [closedBallEval_apply,closedBallJetL_on_smooth j m hj]
      rfl
    rw [hJ k (by omega),hJ k (by omega),hJ (k+1) (by omega)]
    let f := iteratedFDeriv ℝ k b.1
    have hf : ContDiff ℝ ∞ f := (smoothBallData_contDiff b).iteratedFDeriv_right (by simp)
    have hF (z : (X dim)) : fderiv ℝ f z = (iteratedFDeriv ℝ (k+1) b.1 z).curryLeft := rfl
    have hBound (z : (X dim)) (hz : z ∈ closedBall (0 : (X dim)) 1) :
        ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ (ballJetEmbeddingConstant dim) * ‖(denseSmoothBallSobolev dim) m b‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv,
        norm_iteratedFDeriv_iteratedFDeriv b.1 k 2,show 2+k=k+2 by omega]
      rw [← hJ (k+2) (by omega) (⟨z,hz⟩:(UnitClosedBall dim)),closedBallEval_apply]
      exact norm_closedBallJetL_apply_le (k+2) m (by omega) _ _
    rw [← hF]
    exact norm_taylorRemainder_of_second_bound (convex_closedBall _ _) hf
      (mul_nonneg (ballJetEmbeddingConstant_nonneg dim) (norm_nonneg _)) hBound x.property y.property
  rw [← hExpr]
  exact ((denseRange_denseSmoothBallSobolev dim) m).induction hMem hClosed u

set_option maxHeartbeats 1500000 in
theorem hasFDerivWithinAt_closedBallEval (k m : ℕ) (hm : k+dim+3 ≤ m)
    (x : (X dim)) (hx : x ∈ closedBall (0 : (X dim)) 1) :
    HasFDerivWithinAt (𝕜 := ℝ) ((closedBallEval dim) k m)
      ((closedBallEvalCurryL dim) k m ((closedBallEval dim) (k+1) m x))
      (closedBall (0 : (X dim)) 1) x := by
  let C := closedBall (0 : (X dim)) 1
  let L := (closedBallEvalCurryL dim) k m ((closedBallEval dim) (k+1) m x)
  change HasFDerivWithinAt ((closedBallEval dim) k m) L C x
  have hOp (y : (X dim)) (hy : y ∈ C) :
      ‖(closedBallEval dim) k m y - (closedBallEval dim) k m x - L (y-x)‖ ≤
        (ballJetEmbeddingConstant dim) * ‖y-x‖^2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (ballJetEmbeddingConstant_nonneg dim) (sq_nonneg _))
    intro v
    simp only [sub_apply,L,closedBallEvalCurryL_apply]
    have h := closedBallEval_taylor_pointwise k m hm ⟨x,hx⟩ ⟨y,hy⟩ v
    exact h.trans_eq (by simp; ring)
  rw [hasFDerivWithinAt_iff_tendsto]
  have hLim : Tendsto (fun y : (X dim) => (ballJetEmbeddingConstant dim) * ‖y-x‖) (𝓝[C] x) (𝓝 0) := by
    have h : Continuous (fun y : (X dim) => (ballJetEmbeddingConstant dim) * ‖y-x‖) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm)
    simpa only [sub_self,norm_zero,mul_zero] using (h.continuousWithinAt (s := C) (x := x)).tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLim
    (Eventually.of_forall fun _ => by positivity) ?_
  filter_upwards [eventually_mem_nhdsWithin (s := C)] with y hy
  calc
    _ ≤ ‖y-x‖⁻¹ * ((ballJetEmbeddingConstant dim) * ‖y-x‖^2) :=
      mul_le_mul_of_nonneg_left (hOp y hy) (inv_nonneg.mpr (norm_nonneg _))
    _ = (ballJetEmbeddingConstant dim) * ‖y-x‖ := by
      by_cases h : ‖y-x‖ = 0
      · simp [h]
      · field_simp

set_option maxHeartbeats 1000000 in
/-- After retaining sufficiently many graph derivatives, closed-ball
evaluation is differentiable in operator norm through the specified order. -/
theorem contDiffOn_closedBallEval_order (m n : ℕ) :
    ∀ k, k+n+dim+3 ≤ m → ContDiffOn ℝ n ((closedBallEval dim) k m) (closedBall (0 : (X dim)) 1) := by
  intro k hk
  induction n generalizing k with
  | zero =>
    apply contDiffOn_zero.mpr
    intro x hx
    exact (hasFDerivWithinAt_closedBallEval k m (by omega) x hx).continuousWithinAt
  | succ n ih =>
    have hu : UniqueDiffOn ℝ (closedBall (0 : (X dim)) 1) :=
      uniqueDiffOn_convex (convex_closedBall _ _) (by rw [interior_closedBall _ one_ne_zero]; exact ⟨0,by simp⟩)
    have hCurry : ContDiff ℝ n ((closedBallEvalCurryL dim) k m) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := (ClosedBallEval dim) (k+1) m)
        (F := (X dim) →L[ℝ] (ClosedBallEval dim) k m) ((closedBallEvalCurryL dim) k m)
    have hd := hCurry.comp_contDiffOn (ih (k+1) (by omega))
    have h := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hu).mpr
      ⟨by simp,_,hd,fun x hx => hasFDerivWithinAt_closedBallEval k m (by omega) x hx⟩
    exact_mod_cast h

end CalderonN
