module

public import Proof.Manuscript.Lemma81Defs
import Proof.Manuscript.ConformalDifferentiation
import Proof.Manuscript.LocalExtensions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {n : ℕ}
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "axis" => (EuclideanSpace.basisFun (Fin n) ℝ)

theorem propagate_conformal_anchor (hn : 3 ≤ n) {Ω U : Set Eₙ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hU : IsOpen U)
    {F G : Eₙ → Eₙ} {b B : Eₙ → ℝ}
    (hF : SmoothThrough (closure Ω) F) (hb : SmoothThrough (closure Ω) b)
    (hconf : EuclideanConformalOn Ω F b)
    (hG : ContDiffOn ℝ ∞ G U) (hB : ContDiffOn ℝ ∞ B U)
    (hEqG : EqOn G F (U ∩ closure Ω)) (hEqB : EqOn B b (U ∩ closure Ω))
    {p : Eₙ} (hpU : p ∈ U) (hpΩ : p ∈ closure Ω)
    (hpF : F p = p) (hpB : B p = 0)
    (hpDG : fderiv ℝ G p = ContinuousLinearMap.id ℝ Eₙ)
    (hpDB : fderiv ℝ B p = 0) :
    EqOn F id (closure Ω) ∧ EqOn b (fun _ => 0) (closure Ω) := by
  have hFΩ := hF.contDiffOn_interior hΩ
  have hbΩ := hb.contDiffOn_interior hΩ
  obtain ⟨c, hc, _⟩ :=
    exists_const_exp_neg_hessian_of_conformal hn hΩ hconn hFΩ hbΩ hconf
  have hc₀ : c = 0 := by
    let a (x : Eₙ) := Real.exp (-B x) * (∑ i, directional (axis i) B x ^ 2) / 2
    have hcont : ContinuousAt a p := by
      have hBₚ := hB.contDiffAt (hU.mem_nhds hpU)
      have hs (i : Fin n) : ContinuousAt (directional (axis i) B) p :=
        (directional_contDiffAt hBₚ).continuousAt
      have hBcont := hBₚ.continuousAt
      dsimp [a]
      fun_prop
    have heq : EqOn a (fun _ => c) (U ∩ Ω) := by
      intro x hx
      have hderiv := (SmoothThrough.eventuallyEq_extension hU hΩ hx hEqB).fderiv_eq (𝕜 := ℝ)
      simpa only [a, directional, hderiv, hEqB ⟨hx.1, subset_closure hx.2⟩] using hc x hx.2
    have ha := eq_at_closure_of_eqOn_local hU hpU hpΩ hcont continuousAt_const heq
    simpa [a, directional, hpDB] using ha.symm
  have hdb (x : Eₙ) (hx : x ∈ Ω) (i : Fin n) : directional (axis i) b x = 0 := by
    have hz := (hc x hx).trans hc₀
    have hsum : (∑ k, directional (axis k) b x ^ 2) = 0 := by
      have hp := Real.exp_pos (-b x)
      rcases mul_eq_zero.mp (div_eq_zero_iff.mp hz |>.resolve_right (by norm_num)) with h | h
      · exact False.elim (hp.ne' h)
      · exact h
    have hi : directional (axis i) b x ^ 2 ≤ ∑ k, directional (axis k) b x ^ 2 :=
      Finset.single_le_sum (f := fun k => directional (axis k) b x ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hsum] at hi
    exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))
  obtain ⟨bconst, hbconst⟩ := exists_const_of_directional_eq_zero_on hΩ hconn
    (hbΩ.differentiableOn (by simp)) hdb
  have hbcl := eqOn_closure_of_continuousOn hb.continuousOn continuousOn_const hbconst
  have hb₀ : bconst = 0 :=
    (hbcl hpΩ).symm.trans ((hEqB ⟨hpU, hpΩ⟩).symm.trans hpB)
  have hbzero : EqOn b (fun _ => 0) (closure Ω) := hb₀ ▸ hbcl
  have secondF (x : Eₙ) (hx : x ∈ Ω) (i j : Fin n) :
      directional (axis i) (directional (axis j) F) x = 0 := by
    have hx' := hΩ.mem_nhds hx
    rw [directional_directional_of_conformal hΩ hx (hFΩ.contDiffAt hx') (hbΩ.contDiffAt hx') hconf]
    simp only [hdb x hx, conformalConnection, ite_self, zero_add, sub_zero,
      zero_smul, Finset.sum_const_zero]
  have hcols (x : Eₙ) (hx : x ∈ Ω) (i : Fin n) : directional (axis i) F x = axis i := by
    have hFd : DifferentiableOn ℝ (directional (axis i) F) Ω := by
      intro y hy
      exact ((directional_contDiffAt (hFΩ.contDiffAt (hΩ.mem_nhds hy))).differentiableAt
        (by simp)).differentiableWithinAt
    obtain ⟨a, ha⟩ := exists_const_of_directional_eq_zero_on hΩ hconn hFd
      fun y hy j => secondF y hy j i
    have hcont : ContinuousAt (directional (axis i) G) p :=
      (directional_contDiffAt (hG.contDiffAt (hU.mem_nhds hpU))).continuousAt
    have heq : EqOn (directional (axis i) G) (fun _ => a) (U ∩ Ω) := by
      intro y hy
      have he := (SmoothThrough.eventuallyEq_extension hU hΩ hy hEqG).fderiv_eq (𝕜 := ℝ)
      simpa only [directional, he] using ha hy.2
    have hv := eq_at_closure_of_eqOn_local hU hpU hpΩ hcont continuousAt_const heq
    have haxis : axis i = a := by simpa only [directional, hpDG, ContinuousLinearMap.id_apply] using hv
    exact (ha hx).trans haxis.symm
  have hdiff : DifferentiableOn ℝ (fun x => F x - x) Ω :=
    (hFΩ.differentiableOn (by simp)).sub differentiableOn_id
  have hzero (x : Eₙ) (hx : x ∈ Ω) (i : Fin n) : directional (axis i) (fun y => F y - y) x = 0 := by
    change directional (axis i) (fun y => F y - id y) x = 0
    rw [directional, fderiv_fun_sub ((hFΩ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt
      (by simp)) differentiableAt_id]
    simp only [sub_apply, fderiv_id, ContinuousLinearMap.id_apply]
    exact sub_eq_zero.mpr (hcols x hx i)
  obtain ⟨Fconst, hFconst⟩ := exists_const_of_directional_eq_zero_on hΩ hconn hdiff hzero
  have hFcl := eqOn_closure_of_continuousOn (hF.continuousOn.sub continuousOn_id) continuousOn_const hFconst
  have hF₀ : Fconst = 0 := by
    have hv := (hFcl hpΩ).symm
    change Fconst = F p - p at hv
    simpa only [hpF, sub_self] using hv
  refine ⟨fun x hx => ?_, hbzero⟩
  exact sub_eq_zero.mp ((hFcl hx).trans hF₀)

end CalderonPaper
