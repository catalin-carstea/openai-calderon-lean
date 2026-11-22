module

public import Proof.CalderonN.CompactFiniteJets

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! Adapted from `MixedSliceJets` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

variable {P Q F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_iteratedFDeriv_slice_right {f : P × Q → F} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (fun q : P × Q => iteratedFDeriv ℝ k (fun z => f (q.1,z)) q.2) := by
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    (fun _ : Fin k => ContinuousLinearMap.inr ℝ P Q)
  have h := (L.contDiff (n := ∞)).comp (hf.iteratedFDeriv_right (m := ∞) (by simp))
  convert h using 1
  funext q
  exact iteratedFDeriv_slice_right_eq hf q.1 q.2 k

theorem norm_fderiv_iteratedFDeriv_slice_right_le {f : P × Q → F}
    (hf : ContDiff ℝ ∞ f) (p : P) (z : Q) (k : ℕ) (v : P) :
    ‖fderiv ℝ (fun q => iteratedFDeriv ℝ k (fun w => f (q,w)) z) p v‖ ≤
      ‖iteratedFDeriv ℝ (k+1) f (p,z)‖ * ‖v‖ := by
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    (fun _ : Fin k => ContinuousLinearMap.inr ℝ P Q)
  have hL : ‖L‖ ≤ 1 := (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le F _).trans
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ P Q))
  let f' := iteratedFDeriv ℝ k f
  have hf' : ContDiff ℝ ∞ f' := hf.iteratedFDeriv_right (by simp)
  let m (q : P) := (q,z)
  have hM : HasFDerivAt m (ContinuousLinearMap.inl ℝ P Q) p :=
    hasFDerivAt_prodMk_left p z
  have hEq : (fun q => iteratedFDeriv ℝ k (fun w => f (q,w)) z) = L ∘ f' ∘ m :=
    funext (fun q => iteratedFDeriv_slice_right_eq hf q z k)
  rw [hEq,(L.hasFDerivAt.comp p (((hf'.differentiable (by simp) (p,z)).hasFDerivAt).comp p hM)).fderiv]
  rw [← norm_fderiv_iteratedFDeriv]
  change ‖L (fderiv ℝ f' (p,z) (v,0))‖ ≤ ‖fderiv ℝ f' (p,z)‖ * ‖v‖
  calc
    _ ≤ ‖L‖ * ‖fderiv ℝ f' (p,z) (v,0)‖ := L.le_opNorm _
    _ ≤ ‖fderiv ℝ f' (p,z) (v,0)‖ := mul_le_of_le_one_left (norm_nonneg _) hL
    _ ≤ _ := by simpa using (fderiv ℝ f' (p,z)).le_opNorm (v,0)

theorem norm_iteratedFDeriv_slice_left_le {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (q : Q) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun p => f (p,q)) p‖ ≤ ‖iteratedFDeriv ℝ k f (p,q)‖ := by
  rw [iteratedFDeriv_slice_left_eq hf]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => LinearIsometry.inl ℝ P Q)

theorem fderiv_scaled_parameter_eq {f : P → F} (hf : DifferentiableAt ℝ f 0)
    {r : ℝ} (hr : r ≠ 0) (v : P) :
    fderiv ℝ (fun q => f (r⁻¹ • (q-p))) p (r • v) = fderiv ℝ f 0 v := by
  let L : P →L[ℝ] P := r⁻¹ • ContinuousLinearMap.id ℝ P
  have hMap : HasFDerivAt (fun q : P => r⁻¹ • (q-p)) L p :=
    (hasFDerivAt_id p).sub_const p |>.const_smul r⁻¹
  have hd : HasFDerivAt f (fderiv ℝ f 0) (r⁻¹ • (p-p)) := by
    simpa only [sub_self,smul_zero] using hf.hasFDerivAt
  have h := hd.comp p hMap
  change (fderiv ℝ (f ∘ fun q => r⁻¹ • (q-p)) p) (r • v) = _
  rw [h.fderiv]
  simp [L,smul_inv_smul₀ hr]

end CalderonN
