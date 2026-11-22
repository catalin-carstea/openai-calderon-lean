module

public import Proof.CalderonN.MixedSliceJets

import Proof.Manuscript.MixedGreenJets
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {X P Q : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Along a base map with angular coordinate unchanged, one base derivative
uses only the derivative of that map and the first mixed derivative. -/
theorem norm_fderiv_angularJet_comp_base_le
    {a : X → P} (ha : ContDiff ℝ ∞ a) {u : P × Q → ℝ} (hu : ContDiff ℝ ∞ u)
    (y : X) (w : Q) (k : ℕ) {D L : ℝ} (hD : 0 ≤ D)
    (haD : ‖fderiv ℝ a y‖ ≤ D) (hL : 0 ≤ L)
    (hMix : ∀ v : P,
      ‖fderiv ℝ (fun p => iteratedFDeriv ℝ k (fun z => u (p,z)) w) (a y) v‖ ≤ L*‖v‖) :
    ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun x => u (a x,z)) y) w‖ ≤ L*D := by
  let U (p : P) := iteratedFDeriv ℝ k (fun z => u (p,z)) w
  have hU : ContDiff ℝ ∞ U :=
    (CalderonN.contDiff_iteratedFDeriv_slice_right hu k).comp (contDiff_id.prodMk contDiff_const)
  have hf : ContDiff ℝ ∞ (fun t : X × Q => u (a t.1,t.2)) :=
    hu.comp ((ha.comp contDiff_fst).prodMk contDiff_snd)
  refine (Probes.norm_iteratedFDeriv_fderiv_first_slice_le hf y w k).trans ?_
  change ‖fderiv ℝ (U ∘ a) y‖ ≤ L*D
  rw [fderiv_comp y (hU.differentiable (by simp) (a y)) (ha.differentiable (by simp) y)]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hL hD)
  intro v
  rw [ContinuousLinearMap.comp_apply]
  refine (hMix _).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hL
  exact ((fderiv ℝ a y).le_opNorm v).trans (mul_le_mul_of_nonneg_right haD (norm_nonneg _))

/-- Multiplication by a fixed real scalar scales the mixed angular norm. -/
theorem norm_iteratedFDeriv_fderiv_first_slice_const_mul
    (c : ℝ) {u : X × Q → ℝ} (hu : ContDiff ℝ ∞ u) (y : X) (w : Q) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun x => c*u (x,z)) y) w‖ =
      |c| * ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun x => u (x,z)) y) w‖ := by
  have hSlice (z : Q) : DifferentiableAt ℝ (fun x => u (x,z)) y :=
    (hu.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) y
  have hD : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun x => u (x,z)) y) := by
    have hEq (z : Q) : fderiv ℝ (fun x => u (x,z)) y =
        (fderiv ℝ u (y,z)).comp (ContinuousLinearMap.inl ℝ X Q) :=
      (((hu.differentiable (by simp) (y,z)).hasFDerivAt).comp y
        (hasFDerivAt_prodMk_left y z)).fderiv
    simp only [hEq]
    exact ((hu.fderiv_right (m := ∞) (by simp)).comp
      (contDiff_const.prodMk contDiff_id)).clm_comp contDiff_const
  have hEq : (fun z => fderiv ℝ (fun x => c*u (x,z)) y) =
      c • (fun z => fderiv ℝ (fun x => u (x,z)) y) := by
    funext z
    change fderiv ℝ (c • (fun x => u (x,z))) y = _
    exact fderiv_const_smul (hSlice z) c
  rw [hEq]
  change ‖iteratedFDeriv ℝ k (fun z => c • fderiv ℝ (fun x => u (x,z)) y) w‖ = _
  rw [iteratedFDeriv_const_smul_apply' (hD.contDiffAt.of_le (by simp)),norm_smul,Real.norm_eq_abs]

end CalderonPaper
