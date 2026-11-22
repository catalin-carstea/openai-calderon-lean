module

public import Proof.CalderonPatch.NativeBoundaryMetricChart
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.WeakDeriv.Basic

import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Tactic

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace TauCeti
open scoped ContDiff Distributions ENNReal Topology

namespace CalderonPatch

open CalderonN (X I)

variable {n : ℕ} [NeZero n]
local notation "E" => X n

/-- The open coordinate half-space inward from the flat face. -/
abbrev positiveHalfSpaceOpens (n : ℕ) [NeZero n] : Opens (X n) :=
  ⟨positiveHalfSpace n,isOpen_positiveHalfSpace⟩

/-- A smooth cutoff whose transition takes place inside the positive
half-space, away from its boundary. -/
@[expose] def halfSpaceCutoff (c : ℝ) (x : E) : ℝ := Real.smoothTransition (c * x 0 - 1)

theorem contDiff_halfSpaceCutoff (c : ℝ) : ContDiff ℝ ∞ (halfSpaceCutoff (n := n) c) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (EuclideanSpace.proj (𝕜 := ℝ) (0 : I n)).contDiff).sub contDiff_const)

theorem tsupport_halfSpaceCutoff_subset {c : ℝ} (hc : 0 < c) :
    tsupport (halfSpaceCutoff (n := n) c) ⊆ {x : E | 1 / c ≤ x 0} := by
  apply closure_minimal _ (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : I n)).continuous)
  intro x hx
  by_contra hn
  apply hx
  apply Real.smoothTransition.zero_of_nonpos
  have h := lt_of_not_ge hn
  change x 0 < 1 / c at h
  nlinarith [(lt_div_iff₀ hc).1 h]

theorem fderiv_halfSpaceCutoff_tangent (c : ℝ) {v : E} (hv : v 0 = 0) (x : E) :
    fderiv ℝ (halfSpaceCutoff c) x v = 0 := by
  let l := c • EuclideanSpace.proj (𝕜 := ℝ) (0 : I n)
  have hl : HasFDerivAt (fun y : E => l y - 1) l x := l.hasFDerivAt.sub_const 1
  have ht := (Real.smoothTransition.contDiff (n := 1) |>.differentiable one_ne_zero
    (l x - 1)).hasFDerivAt.comp x hl
  change fderiv ℝ ((Real.smoothTransition : ℝ → ℝ) ∘ (fun y : E => l y - 1)) x v = 0
  rw [ht.fderiv,ContinuousLinearMap.comp_apply]
  simp [l,hv]

private theorem tendsto_integral_halfSpaceCutoff_mul {F : E → ℝ} (hF : Integrable F)
    (hF0 : ∀ x ∉ positiveHalfSpace n, F x = 0) :
    Tendsto (fun k : ℕ => ∫ x, halfSpaceCutoff ((k : ℝ) + 1) x * F x) atTop (𝓝 (∫ x, F x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
    (fun _ => (contDiff_halfSpaceCutoff _).continuous.aestronglyMeasurable.mul hF.1) hF.norm
    (fun _ => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · rw [norm_mul,halfSpaceCutoff,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)
  · by_cases hx : x ∈ positiveHalfSpace n
    · have ht : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * x 0 - 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _
          ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
            (mem_positiveHalfSpace.mp hx))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ht.eventually_ge_atTop 1] with k hk
      simp [halfSpaceCutoff,Real.smoothTransition.one_of_one_le hk]
    · simp [hF0 x hx]

/-- Zero extension commutes with a weak derivative tangential to the
flat face. The normal cutoff contributes no derivative term. -/
theorem hasWeakLineDerivOn_top_of_positiveHalfSpace
    {w d : E → ℝ} {v : E}
    (h : HasWeakLineDerivOn volume ⟨positiveHalfSpace n,isOpen_positiveHalfSpace⟩ w d v)
    (hv : v 0 = 0) (hw : LocallyIntegrable w volume) (hd : LocallyIntegrable d volume)
    (hw0 : ∀ x ∉ positiveHalfSpace n, w x = 0)
    (hd0 : ∀ x ∉ positiveHalfSpace n, d x = 0) :
    HasWeakLineDerivOn volume ⊤ w d v := by
  refine (hasWeakLineDerivOn_iff_testFunction).2
    ⟨inferInstance,hw.locallyIntegrableOn _,hd.locallyIntegrableOn _,fun φ => ?_⟩
  let L (x : E) := lineDeriv ℝ (φ : E → ℝ) x v * w x
  let R (x : E) := φ x * d x
  have hL : Integrable L := by
    simpa only [L,smul_eq_mul] using
      integrable_lineDeriv_smul_of_locallyIntegrableOn (hw.locallyIntegrableOn _) φ v
  have hR : Integrable R := by
    simpa only [R,smul_eq_mul] using integrable_smul_of_locallyIntegrableOn (hd.locallyIntegrableOn _) φ
  have htest (k : ℕ) :
      (∫ x, halfSpaceCutoff ((k : ℝ) + 1) x * L x) =
        -∫ x, halfSpaceCutoff ((k : ℝ) + 1) x * R x := by
    let c : ℝ := (k : ℝ) + 1
    have hc : 0 < c := by positivity
    let χ := halfSpaceCutoff (n := n) c
    let θ : 𝓓(⟨positiveHalfSpace n,isOpen_positiveHalfSpace⟩,ℝ) :=
      ⟨χ * φ,(contDiff_halfSpaceCutoff c).mul φ.contDiff,φ.hasCompactSupport.mul_left,
        tsupport_mul_subset_left.trans ((tsupport_halfSpaceCutoff_subset hc).trans
          (fun x hx => mem_positiveHalfSpace.mpr ((div_pos one_pos hc).trans_le hx)))⟩
    have hθ : (θ : E → ℝ) = χ * φ := rfl
    have hδ (x : E) :
        lineDeriv ℝ (θ : E → ℝ) x v = χ x * lineDeriv ℝ (φ : E → ℝ) x v := by
      have hχx := ((contDiff_halfSpaceCutoff (n := n) c).differentiable (by simp) x)
      have hφx := φ.contDiff.differentiable (by simp) x
      have hmul := hχx.mul hφx
      rw [hθ,hmul.lineDeriv_eq_fderiv,hφx.lineDeriv_eq_fderiv,fderiv_mul hχx hφx]
      simp [χ,fderiv_halfSpaceCutoff_tangent c hv]
    have hIBP := h.integral_lineDeriv_smul_eq_neg_integral_smul θ
    simp_rw [hδ] at hIBP
    simpa only [L,R,χ,c,hθ,Pi.mul_apply,smul_eq_mul,mul_assoc] using hIBP
  have hlt := (tendsto_integral_halfSpaceCutoff_mul hL (fun x hx => by simp [L,hw0 x hx])).congr htest
  have hrt := (tendsto_integral_halfSpaceCutoff_mul hR (fun x hx => by simp [R,hd0 x hx])).neg
  simpa only [L,R,smul_eq_mul] using tendsto_nhds_unique hlt hrt

end CalderonPatch
