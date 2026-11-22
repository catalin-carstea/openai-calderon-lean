module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

import Mathlib.Topology.Piecewise

@[expose] public section

noncomputable section
open Asymptotics Filter Set
open scoped ContDiff Topology

namespace CalderonPatch

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem hasFDerivAt_piecewise_of_same_derivative
    {S : Set E} [∀ x, Decidable (x ∈ S)] {f g : E → F} {x : E} {A : E →L[ℝ] F}
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g A x) (h : f x = g x) :
    HasFDerivAt (S.piecewise f g) A x := by
  have hx : S.piecewise f g x = f x := by by_cases hS : x ∈ S <;> simp [hS, h]
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff] at hf hg ⊢
  intro c hc
  filter_upwards [hf hc, hg hc] with y hyf hyg
  by_cases hy : y ∈ S
  · rw [piecewise_eq_of_mem _ _ _ hy, hx]
    exact hyf
  · rw [piecewise_eq_of_notMem _ _ _ hy, hx, h]
    exact hyg

private theorem hasFDerivAt_piecewise_of_frontier
    {S : Set E} [∀ x, Decidable (x ∈ S)] {f g : E → F}
    {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (h₀ : x ∈ frontier S → f x = g x)
    (h₁ : x ∈ frontier S → fderiv ℝ f x = fderiv ℝ g x) :
    HasFDerivAt (S.piecewise f g) (S.piecewise (fderiv ℝ f) (fderiv ℝ g) x) x := by
  by_cases hx : x ∈ frontier S
  · have hd : S.piecewise (fderiv ℝ f) (fderiv ℝ g) x = fderiv ℝ f x := by
      by_cases hS : x ∈ S <;> simp [hS, h₁ hx]
    rw [hd]
    exact hasFDerivAt_piecewise_of_same_derivative hf.hasFDerivAt
      ((h₁ hx).symm ▸ hg.hasFDerivAt) (h₀ hx)
  · by_cases hS : x ∈ S
    · have hInt := (mem_interior_iff_notMem_frontier hS).mpr hx
      rw [piecewise_eq_of_mem _ _ _ hS]
      apply hf.hasFDerivAt.congr_of_eventuallyEq
      filter_upwards [isOpen_interior.mem_nhds hInt] with y hy
      exact piecewise_eq_of_mem _ _ _ (interior_subset hy)
    · have hInt : x ∈ interior Sᶜ := (mem_interior_iff_notMem_frontier hS).mpr
        (by rwa [frontier_compl])
      rw [piecewise_eq_of_notMem _ _ _ hS]
      apply hg.hasFDerivAt.congr_of_eventuallyEq
      filter_upwards [isOpen_interior.mem_nhds hInt] with y hy
      exact piecewise_eq_of_notMem _ _ _ (interior_subset hy)

/-- Functions whose full jets match at the frontier can be pasted with
preservation of each finite order of smoothness. -/
theorem contDiffOn_nat_piecewise_of_matched_jets
    {S U : Set E} [∀ x, Decidable (x ∈ S)] (hU : IsOpen U) (k : ℕ) {f g : E → F}
    (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U)
    (hJ : ∀ j ≤ k, EqOn (iteratedFDeriv ℝ j f) (iteratedFDeriv ℝ j g) (U ∩ frontier S)) :
    ContDiffOn ℝ k (S.piecewise f g) U := by
  induction k generalizing F with
  | zero =>
    have h₀ : EqOn f g (U ∩ frontier S) := by
      intro x hx
      have h := congrArg (fun A : E [×0]→L[ℝ] F => A (fun i => Fin.elim0 i)) (hJ 0 le_rfl hx)
      simpa only [iteratedFDeriv_zero_apply] using h
    exact contDiffOn_zero.mpr (ContinuousOn.piecewise (fun _ hx => h₀ hx)
      (hf.continuousOn.mono inter_subset_left) (hg.continuousOn.mono inter_subset_left))
  | succ k ih =>
    have h₀ : EqOn f g (U ∩ frontier S) := by
      intro x hx
      have h := congrArg (fun A : E [×0]→L[ℝ] F => A (fun i => Fin.elim0 i)) (hJ 0 (Nat.zero_le _) hx)
      simpa only [iteratedFDeriv_zero_apply] using h
    have h₁ : EqOn (fderiv ℝ f) (fderiv ℝ g) (U ∩ frontier S) := by
      intro x hx
      ext v
      have h := congrArg (fun A : E [×1]→L[ℝ] F => A (fun _ => v)) (hJ 1 (Nat.succ_le_succ (Nat.zero_le _)) hx)
      simpa only [iteratedFDeriv_one_apply] using h
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU] at hf hg ⊢
    have hD (x : E) (hx : x ∈ U) :=
      hasFDerivAt_piecewise_of_frontier (hf.1.differentiableAt (hU.mem_nhds hx))
        (hg.1.differentiableAt (hU.mem_nhds hx)) (fun h => h₀ ⟨hx, h⟩) (fun h => h₁ ⟨hx, h⟩)
    have hF : EqOn (fderiv ℝ (S.piecewise f g)) (S.piecewise (fderiv ℝ f) (fderiv ℝ g)) U :=
      fun x hx => (hD x hx).fderiv
    refine ⟨fun x hx => (hD x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    apply (ih hf.2.2 hg.2.2 _).congr hF
    intro j hj x hx
    have h := hJ (j + 1) (Nat.succ_le_succ hj) hx
    simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply] at h
    exact (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.injective h

/-- Infinite-order matching along the seam makes the pasted function
smooth on the open collar. -/
theorem contDiffOn_piecewise_of_matched_jets
    {S U : Set E} [∀ x, Decidable (x ∈ S)] (hU : IsOpen U) {f g : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hJ : ∀ j, EqOn (iteratedFDeriv ℝ j f) (iteratedFDeriv ℝ j g) (U ∩ frontier S)) :
    ContDiffOn ℝ ∞ (S.piecewise f g) U := by
  rw [contDiffOn_infty] at hf hg ⊢
  exact fun k => contDiffOn_nat_piecewise_of_matched_jets hU k (hf k) (hg k) (fun j _ => hJ j)

theorem contDiff_piecewise_of_matched_jets
    {S : Set E} [∀ x, Decidable (x ∈ S)] {f g : E → F}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hJ : ∀ j, EqOn (iteratedFDeriv ℝ j f) (iteratedFDeriv ℝ j g) (frontier S)) :
    ContDiff ℝ ∞ (S.piecewise f g) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_piecewise_of_matched_jets isOpen_univ hf.contDiffOn hg.contDiffOn
    (fun j => (hJ j).mono inter_subset_right)

end CalderonPatch
