/-
The compact uniform Taylor remainder follows DNNormalTaylorBound.lean in the conformal
Poisson Lean release at commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd, BSD 3-Clause.
The continuity and chain rule for the normal derivatives use smoothness.
-/
module

public import Mathlib.Analysis.Calculus.Taylor

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

public section

noncomputable section

open Set Finset
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The normal derivatives of a smooth function on an open signed collar
are the ambient iterated derivatives on the repeated vertical vector. -/
theorem iteratedDeriv_slice_eq_iteratedFDeriv {O : Set (E × ℝ)} (hO : IsOpen O)
    {G : E × ℝ → F} (hG : ContDiffOn ℝ ∞ G O)
    {y : E} {t : ℝ} (hx : (y,t) ∈ O) (j : ℕ) :
    iteratedDeriv j (fun s : ℝ => G (y,s)) t =
      iteratedFDeriv ℝ j G (y,t) (fun _ => ((0 : E), (1 : ℝ))) := by
  let L := ContinuousLinearMap.inr ℝ E ℝ
  let a : E × ℝ := (y,0)
  let U := (fun z : E × ℝ => a + z) ⁻¹' O
  let g := fun z : E × ℝ => G (a + z)
  have ha (s : ℝ) : a + L s = (y,s) := by simp [a,L]
  have hU : IsOpen U := hO.preimage (continuous_const.add continuous_id)
  have hUL : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hg : ContDiffOn ℝ ∞ g U :=
    hG.comp (contDiff_const.add contDiff_id).contDiffOn (mapsTo_preimage _ _)
  have hLt : L t ∈ U := by simpa only [U, Set.mem_preimage, ha] using hx
  have hh := L.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hUL.uniqueDiffOn hLt
    (by simp : (j : ℕ∞ω) ≤ ∞)
  have hcomp : g ∘ L = fun s : ℝ => G (y,s) := by
    funext s
    exact congrArg G (ha s)
  have hgAt : ContDiffAt ℝ j g (L t) :=
    (hg.of_le (by simp)).contDiffAt (hU.mem_nhds hLt)
  have hcompAt : ContDiffAt ℝ j (g ∘ L) t := hgAt.comp t L.contDiff.contDiffAt
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hUL.uniqueDiffOn hcompAt hLt,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hgAt hLt, hcomp] at hh
  rw [iteratedDeriv_eq_iteratedFDeriv, hh]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ j (fun z => G (a + z)) (L t) (fun _ => L 1) = _
  rw [iteratedFDeriv_comp_add_left, ha]
  rfl

/-- Evaluation of each repeated ambient directional derivative is
smooth wherever the coefficients are smooth. -/
theorem contDiffOn_iteratedFDeriv_repeat {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {O : Set A} (hO : IsOpen O) {G : A → F} (hG : ContDiffOn ℝ ∞ G O) (v : A) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun x => iteratedFDeriv ℝ j G x (fun _ => v)) O := by
  induction j with
  | zero => simpa only [iteratedFDeriv_zero_apply] using hG
  | succ j ih =>
    have hd := (ih.fderiv_of_isOpen hO (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))).clm_apply
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : A => v) O)
    apply hd.congr
    intro x hx
    have hj : DifferentiableAt ℝ (iteratedFDeriv ℝ j G) x :=
      (hG.contDiffAt (hO.mem_nhds hx)).differentiableAt_iteratedFDeriv (by exact_mod_cast (show (j : ℕ∞) < ⊤ by simp))
    exact hj.iteratedFDeriv_succ_apply_left'

/-- The normal Taylor coefficients are smooth functions of the face
coordinates. -/
theorem contDiffOn_normalTaylorCoeff {O : Set (E × ℝ)} (hO : IsOpen O)
    {G : E × ℝ → F} (hG : ContDiffOn ℝ ∞ G O) {U : Set E}
    (hU : MapsTo (fun y : E => (y, (0 : ℝ))) U O) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun y => iteratedDeriv j (fun t : ℝ => G (y,t)) 0) U := by
  have H := contDiffOn_iteratedFDeriv_repeat hO hG ((0 : E), (1 : ℝ)) j
  refine (H.comp (contDiff_id.prodMk contDiff_const).contDiffOn hU).congr ?_
  exact fun y hy => iteratedDeriv_slice_eq_iteratedFDeriv hO hG (hU hy) j

/-- Taylor expansion in the normal coordinate, with a uniform
power remainder on a compact finite collar. -/
theorem exists_uniform_normal_taylor_bound
    {O : Set (E × ℝ)} (hO : IsOpen O) {G : E × ℝ → F} (hG : ContDiffOn ℝ ∞ G O)
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hrect : K ×ˢ Icc (0 : ℝ) r ⊆ O) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ t ∈ Icc (0 : ℝ) r,
      ‖G (y,t) - ∑ j ∈ range (N + 1),
        (t ^ j / (j.factorial : ℝ)) • iteratedDeriv j (fun s : ℝ => G (y,s)) 0‖ ≤
        C * t ^ (N + 1) := by
  let J (x : E × ℝ) := iteratedFDeriv ℝ (N + 1) G x (fun _ => ((0 : E), (1 : ℝ)))
  have hEq : EqOn (iteratedFDerivWithin ℝ (N + 1) G O) (iteratedFDeriv ℝ (N + 1) G) O :=
    fun x hx => iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
      ((hG.of_le (by simp)).contDiffAt (hO.mem_nhds hx)) hx
  have hDerivative : ContinuousOn (iteratedFDeriv ℝ (N + 1) G) O :=
    (hG.continuousOn_iteratedFDerivWithin (by simp) hO.uniqueDiffOn).congr
      (fun x hx => (hEq hx).symm)
  have heval : Continuous (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin (N + 1) => E × ℝ) F =>
      L (fun _ => ((0 : E), (1 : ℝ)))) := by fun_prop
  have hjet : ContinuousOn J O := heval.comp_continuousOn hDerivative
  obtain ⟨M,hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn (hjet.mono hrect)
  let B : ℝ := max 0 M
  have hB : 0 ≤ B := le_max_left _ _
  have hfac : 0 < (N.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
  refine ⟨B / (N.factorial : ℝ), div_nonneg hB hfac.le, ?_⟩
  intro y hy t ht
  have hsmooth : ∀ s ∈ Icc (0 : ℝ) r, ContDiffAt ℝ ∞ (fun a : ℝ => G (y,a)) s := by
    intro s hs
    exact (hG.contDiffAt (hO.mem_nhds (hrect ⟨hy, hs⟩))).comp s
      (contDiffAt_const.prodMk contDiffAt_id)
  have h0 : (0 : ℝ) ∈ Icc 0 r := ⟨le_rfl,hr.le⟩
  have huni : UniqueDiffOn ℝ (Icc (0 : ℝ) r) := uniqueDiffOn_Icc hr
  have hbound : ∀ s ∈ Icc (0 : ℝ) r,
      ‖iteratedDerivWithin (N + 1) (fun a : ℝ => G (y,a)) (Icc (0 : ℝ) r) s‖ ≤ B := by
    intro s hs
    rw [iteratedDerivWithin_eq_iteratedDeriv huni ((hsmooth s hs).of_le (by simp)) hs,
      iteratedDeriv_slice_eq_iteratedFDeriv hO hG (hrect ⟨hy,hs⟩)]
    exact (hM (y,s) ⟨hy,hs⟩).trans (le_max_right _ _)
  have hp : taylorWithinEval (fun a : ℝ => G (y,a)) N (Icc (0 : ℝ) r) 0 t =
      ∑ j ∈ range (N + 1), (t ^ j / (j.factorial : ℝ)) • iteratedDeriv j (fun s : ℝ => G (y,s)) 0 := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro j hj
    rw [iteratedDerivWithin_eq_iteratedDeriv huni ((hsmooth 0 h0).of_le (by simp)) h0]
    simp only [sub_zero, div_eq_mul_inv, mul_comm]
  have hb := taylor_mean_remainder_bound hr.le
    (fun s hs => ((hsmooth s hs).of_le (by simp)).contDiffWithinAt) ht hbound
  rw [hp] at hb
  simpa only [sub_zero, div_mul_eq_mul_div] using hb

end CalderonPatch.BoundaryLayer
