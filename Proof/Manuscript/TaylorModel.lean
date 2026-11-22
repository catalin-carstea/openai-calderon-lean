module

public import Proof.CalderonN.CompactSmoothExtension

import Proof.CalderonN.TaylorJetSymmetry
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Tactic

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonPaper

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A separate smooth spatial family can be replaced at a fixed spatial
point by a jointly smooth function with the same finite spatial jets.
The identities hold on a neighborhood in the parameter. -/
theorem exists_smooth_spatial_jet_model {b : P → X → ℝ} (hb : ∀ q, ContDiff ℝ ∞ (b q))
    {V : Set P} (hV : IsOpen V) {p : P} (hp : p ∈ V) (w : X) (N : ℕ)
    (hJet : ∀ j ≤ N, ContDiffOn ℝ ∞ (fun q => iteratedFDeriv ℝ j (b q) w) V) :
    ∃ B : P × X → ℝ, ContDiff ℝ ∞ B ∧
      ∀ᶠ q in 𝓝 p, ∀ j ≤ N,
        iteratedFDeriv ℝ j (fun z => B (q,z)) w = iteratedFDeriv ℝ j (b q) w := by
  classical
  have hExt (j : Fin (N+1)) :
      ∃ A : P → (X [×j.val]→L[ℝ] ℝ), ContDiff ℝ ∞ A ∧
        A =ᶠ[𝓝 p] (fun q => iteratedFDeriv ℝ j.val (b q) w) := by
    obtain ⟨A,hA,_,U,hU,hpU,_,hEq⟩ := CalderonN.exists_contDiff_extension_near_compact
      hV isCompact_singleton (singleton_subset_iff.mpr hp) (hJet j.val (by omega))
    exact ⟨A,hA,hEq.eventuallyEq_of_mem (hU.mem_nhds (hpU (mem_singleton p)))⟩
  choose A hA hAgree using hExt
  let B (q : P × X) : ℝ :=
    ∑ j : Fin (N+1), (j.val.factorial : ℝ)⁻¹ * A j q.1 (fun _ => q.2-w)
  have hB : ContDiff ℝ ∞ B := by
    apply ContDiff.sum
    intro j hj
    let L := ContinuousLinearMap.smulRightL ℝ ℝ X (ContinuousLinearMap.id ℝ ℝ)
    let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin j.val => ℝ) (fun _ => X) ℝ
    let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j.val => ℝ) ℝ (fun _ => 1)
    have hL : ContDiff ℝ ∞ (fun q : P × X => fun _ : Fin j.val => L (q.2-w)) :=
      contDiff_pi.mpr fun _ => L.contDiff.comp (contDiff_snd.sub contDiff_const)
    have hE := E.contDiff.comp ((C.contDiff.comp hL).clm_apply ((hA j).comp contDiff_fst))
    apply contDiff_const.mul
    convert hE using 1
    funext q
    change A j q.1 (fun _ => q.2-w) = A j q.1 (fun _ => (1 : ℝ) • (q.2-w))
    simp only [one_smul]
  refine ⟨B,hB,?_⟩
  filter_upwards [eventually_all.mpr hAgree] with q hq j hj
  let S : FormalMultilinearSeries ℝ X ℝ := fun k =>
    if h : k < N+1 then (k.factorial : ℝ)⁻¹ • A ⟨k,h⟩ q else 0
  have hfinite (k : ℕ) (hk : N+1 ≤ k) : S k = 0 := by
    simp only [S,dite_eq_right (not_lt.mpr hk)]
  have hser : HasFiniteFPowerSeriesOnBall (fun z => B (q,z)) S w (N+1) ⊤ := by
    apply HasFiniteFPowerSeriesOnBall.mk' hfinite (by simp)
    intro z hz
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [B, add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [S,dite_eq_left k.isLt,Fin.eta,smul_apply,smul_eq_mul]
  ext v
  rw [hser.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace v]
  have hlt : j < N+1 := by omega
  simp only [S,dite_eq_left hlt,smul_apply,smul_eq_mul,hq ⟨j,hlt⟩]
  have hSym (σ : Equiv.Perm (Fin j)) :
      iteratedFDeriv ℝ j (b q) w (fun i => v (σ i)) =
        iteratedFDeriv ℝ j (b q) w v := by
    change iteratedFDeriv ℝ j (b q) w (v ∘ σ) = _
    simpa only [iteratedFDerivWithin_univ,interior_univ,closure_univ] using
      CalderonN.iteratedFDerivWithin_perm (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set X))
        (by simp) (hb q).contDiffOn j w (mem_univ w) v σ
  simp_rw [hSym]
  simp [Fintype.card_perm, Nat.factorial_ne_zero]

end CalderonPaper
