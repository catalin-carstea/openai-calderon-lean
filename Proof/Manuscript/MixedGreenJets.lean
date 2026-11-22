module

public import Proof.CalderonN.MixedSliceJets

import all Proof.CalderonN.LocalMixedParameterJetCalculus
import Mathlib.Tactic

public section

open CalderonN
open scoped BigOperators
open scoped ContDiff

namespace CalderonPaper.Probes

variable {P Q F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem fderiv_first_slice {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (w : Q) (v : P) :
    fderiv ℝ (fun q => f (q,w)) p v = fixedDirectionalDerivative f (v,0) (p,w) := by
  change fderiv ℝ (f ∘ fun q => (q,w)) p v = _
  rw [(((hf.differentiable (by simp) (p,w)).hasFDerivAt).comp p
    (hasFDerivAt_prodMk_left p w)).fderiv]
  rfl

/-- Move one parameter derivative across any finite angular derivative. -/
theorem apply_iteratedFDeriv_fderiv_first_slice {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (w : Q) (k : ℕ) (m : Fin k → Q) (v : P) :
    (iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun q => f (q,z)) p) w m) v =
      (fderiv ℝ (fun q => iteratedFDeriv ℝ k (fun z => f (q,z)) w) p v) m := by
  let h (z : Q) := fderiv ℝ (fun q => f (q,z)) p
  let d := fixedDirectionalDerivative f (v,0)
  let m' := fun i => ((0:P),m i)
  let H (q : P) := iteratedFDeriv ℝ k (fun z => f (q,z)) w
  let A := ContinuousLinearMap.apply ℝ F v
  let B := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Q) F m
  have hd₁ : ContDiff ℝ ∞ d := contDiff_fixedDirectionalDerivative f hf (v,0)
  have hh : ContDiff ℝ ∞ h := by
    let K : P × Q → (P →L[ℝ] F) :=
      fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ P Q)
    have hK : ContDiff ℝ ∞ K :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
    have he : h = fun z => K (p,z) := by
      funext z
      exact (((hf.differentiable (by simp) (p,z)).hasFDerivAt).comp p
        (hasFDerivAt_prodMk_left p z)).fderiv
    rw [he]
    exact hK.comp (contDiff_const.prodMk contDiff_id)
  have hH : ContDiff ℝ ∞ H :=
    (contDiff_iteratedFDeriv_slice_right hf k).comp (contDiff_id.prodMk contDiff_const)
  have hBd (q : P) : B (H q) = fixedJetEval k m' f (q,w) := by
    rw [fixedJetEval_eq_iteratedFDeriv _ _ _ hf]
    show iteratedFDeriv ℝ k (fun z => f (q,z)) w m = _
    rw [iteratedFDeriv_slice_right_eq hf]
    rfl
  calc
    _ = iteratedFDeriv ℝ k (A ∘ h) w m := by
      rw [A.iteratedFDeriv_comp_left hh.contDiffAt (by simp)]
      rfl
    _ = iteratedFDeriv ℝ k (fun z => d (p,z)) w m := by
      rw [show A ∘ h = (fun z => d (p,z)) from funext (fun z => fderiv_first_slice hf p z v)]
    _ = fixedJetEval k m' d (p,w) := by
      rw [iteratedFDeriv_slice_right_eq hd₁, fixedJetEval_eq_iteratedFDeriv _ _ _ hd₁]
      rfl
    _ = fixedDirectionalDerivative (fixedJetEval k m' f) (v,0) (p,w) := by
      rw [fixedDirectionalDerivative_fixedJetEval k m' f hf]
    _ = fderiv ℝ (B ∘ H) p v := by
      rw [← fderiv_first_slice (contDiff_fixedJetEval k m' f hf) p w v]
      rw [show (fun q => fixedJetEval k m' f (q,w)) = B ∘ H from funext (fun q => (hBd q).symm)]
    _ = _ := by
      rw [(B.hasFDerivAt.comp p (hH.differentiable (by simp) p).hasFDerivAt).fderiv]
      rfl

theorem norm_iteratedFDeriv_fderiv_first_slice_le {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (w : Q) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun q => f (q,z)) p) w‖ ≤
      ‖fderiv ℝ (fun q => iteratedFDeriv ℝ k (fun z => f (q,z)) w) p‖ := by
  let D := fderiv ℝ (fun q => iteratedFDeriv ℝ k (fun z => f (q,z)) w) p
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg D)
  intro m
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [apply_iteratedFDeriv_fderiv_first_slice hf]
  calc
    ‖D v m‖ ≤ ‖D v‖ * ∏ i, ‖m i‖ := (D v).le_opNorm m
    _ ≤ (‖D‖ * ‖v‖) * ∏ i, ‖m i‖ :=
      mul_le_mul_of_nonneg_right (D.le_opNorm v) (by positivity)
    _ = (‖D‖ * ∏ i, ‖m i‖) * ‖v‖ := by ring

end CalderonPaper.Probes
