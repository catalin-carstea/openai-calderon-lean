module

public import Proof.CalderonN.ActualSignedAdjoint

import Proof.CalderonN.CoordinateJets
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-! Adapted from `ActualSignedHorizontal` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1700000

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def actualSignedAngularLift (γ : (MetricField dim)) (e : (Frame dim)) (lam : ℝ) (r : (X dim) → ℝ)
    (q : (X dim) × (X dim)) : (SignedNormalParameter dim) × (X dim) :=
  (actualSignedNormalParameter lam r q.1,(movingBallToFrame γ e q).2)

theorem contDiff_actualSignedAngularLift {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) (lam : ℝ)
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (actualSignedAngularLift γ e lam r) := by
  have hb : ContDiff ℝ ∞ (fun q : (X dim) × (X dim) => fun k : (I dim) => coordDeriv k r q.1) :=
    contDiff_pi.mpr fun k =>
      (((hr.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const (c := axis k)))).comp contDiff_fst
  have hF := (contDiff_movingBallToFrame hγ he).snd
  exact (contDiff_const.prodMk (contDiff_fst.prodMk ((hr.comp contDiff_fst).prodMk hb))).prodMk hF

/-- Bounds for the coordinate jets of the shrinking radius control the
pullback of a smooth signed angular datum along horizontal directions. -/
theorem norm_horizontal_actualSignedAngularLift_le
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} (he : ∀ k, ContDiff ℝ ∞ (fun y => e y k)) (lam : ℝ)
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) (i : (I dim)) (q : (X dim) × (X dim))
    {D M B : ℝ} (hD : 0 ≤ D) (hM : 1 ≤ M)
    (hr₁ : |coordDeriv i r q.1| ≤ D)
    (hr₂ : ∀ j, |coordDeriv i (coordDeriv j r) q.1| ≤ D)
    (hConn : ‖connection γ q.1 (axis i) q.2‖ ≤ M)
    (hFrame : ‖fderiv ℝ (fun z => (movingBallToFrame γ e z).2) q‖ ≤ M)
    {f : (SignedNormalParameter dim) × (X dim) → ℝ}
    (hf : DifferentiableAt ℝ f (actualSignedAngularLift γ e lam r q))
    (hB : ‖fderiv ℝ f (actualSignedAngularLift γ e lam r q)‖ ≤ B) :
    ‖horizontal γ (fun z => (f (actualSignedAngularLift γ e lam r z) : ℂ)) q.1 q.2
      (axis i)‖ ≤ B * max D (M^2) := by
  let d : (X dim) × (X dim) := (axis i,-connection γ q.1 (axis i) q.2)
  let c (t : ℝ) := q+t • d
  let W (z : (X dim) × (X dim)) := (movingBallToFrame γ e z).2
  let L := actualSignedAngularLift γ e lam r
  let v : (SignedNormalParameter dim) × (X dim) :=
    ((0,(axis i,(coordDeriv i r q.1,fun j => coordDeriv i (coordDeriv j r) q.1))),
      fderiv ℝ W q d)
  have hL := (contDiff_actualSignedAngularLift hγ he lam hr).differentiable (by simp) q
  have hc₀ : c 0 = q := by simp [c]
  have hc : HasDerivAt c d 0 := by
    simpa only [c,id_eq,ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
      ((((hasDerivAt_id (0:ℝ)).smul_const d).hasFDerivAt.const_add q :
        HasFDerivAt _ _ (0:ℝ)).hasDerivAt)
  have hcBase : HasDerivAt (fun t => (c t).1) (axis i) 0 := hc.fst
  have hAlong (u : (X dim) → ℝ) (hu : ContDiff ℝ ∞ u) :
      HasDerivAt (fun t => u (c t).1) (coordDeriv i u q.1) 0 := by
    have hd : HasFDerivAt u (fderiv ℝ u q.1) (c 0).1 := hc₀.symm ▸
      (hu.differentiable (by simp) q.1).hasFDerivAt
    exact hd.comp_hasDerivAt 0 hcBase
  have hb (j : (I dim)) : ContDiff ℝ ∞ (coordDeriv j r) :=
    (hr.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hb' : HasDerivAt (fun t => fun j : (I dim) => coordDeriv j r (c t).1)
      (fun j => coordDeriv i (coordDeriv j r) q.1) 0 :=
    hasDerivAt_pi.mpr (fun j => hAlong _ (hb j))
  have hW : HasFDerivAt W (fderiv ℝ W q) (c 0) := hc₀.symm ▸
    ((contDiff_movingBallToFrame hγ he).snd.differentiable (by simp) q).hasFDerivAt
  have hd₁ : HasDerivAt (L ∘ c) v 0 :=
    (((hasDerivAt_const 0 lam).prodMk (hcBase.prodMk ((hAlong r hr).prodMk hb'))).prodMk
      (hW.comp_hasDerivAt 0 hc))
  have hd₂ : HasFDerivAt L (fderiv ℝ L q) (c 0) := hc₀.symm ▸ hL.hasFDerivAt
  have hv := (hd₂.comp_hasDerivAt 0 hc).unique hd₁
  have hd : ‖d‖ ≤ M := by
    rw [Prod.norm_def]
    exact max_le ((norm_axis i).trans_le hM) (by simpa only [d, norm_neg] using hConn)
  have hWb : ‖fderiv ℝ W q d‖ ≤ M^2 :=
    ((fderiv ℝ W q).le_opNorm d).trans
      ((mul_le_mul hFrame hd (norm_nonneg _) (zero_le_one.trans hM)).trans_eq (by ring))
  have hb₂ : ‖fun j => coordDeriv i (coordDeriv j r) q.1‖ ≤ D :=
    (pi_norm_le_iff_of_nonneg hD).mpr (fun j => by simpa only [Real.norm_eq_abs] using hr₂ j)
  have hMsq : 1 ≤ M^2 := one_le_pow₀ hM
  have hBv : ‖v‖ ≤ max D (M^2) := by
    simp only [v,Prod.norm_def,norm_zero,norm_axis,Real.norm_eq_abs,max_le_iff]
    exact ⟨⟨(zero_le_one.trans hMsq).trans (le_max_right _ _),
      ⟨hMsq.trans (le_max_right _ _),
        ⟨hr₁.trans (le_max_left _ _),hb₂.trans (le_max_left _ _)⟩⟩⟩,
      hWb.trans (le_max_right _ _)⟩
  have hComp := (Complex.ofRealCLM.hasFDerivAt.comp q (hf.hasFDerivAt.comp q hL.hasFDerivAt)).fderiv
  change ‖fderiv ℝ (Complex.ofRealCLM ∘ f ∘ L) q d‖ ≤ _
  rw [hComp]
  change ‖(fderiv ℝ f (L q) (fderiv ℝ L q d) : ℂ)‖ ≤ _
  rw [hv,Complex.norm_real]
  exact ((fderiv ℝ f (L q)).le_opNorm v).trans
    (mul_le_mul hB hBv (norm_nonneg _) ((norm_nonneg _).trans hB))

end CalderonN
