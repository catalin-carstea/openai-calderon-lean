module

public import Proof.Manuscript.MovingTrace.PolynomialProfileJets
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonPatch.BoundaryLayer Set
open scoped ContDiff

namespace CalderonPaper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Scales the inward distance while keeping angular and auxiliary geometry
parameters fixed. Every differentiation costs at most one inverse scale. -/
def scaleNormal (h : ℝ) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod (h⁻¹ • ContinuousLinearMap.snd ℝ E ℝ)

theorem scaleNormal_apply (h : ℝ) (q : E × ℝ) :
    scaleNormal h q = (q.1,q.2 / h) := by
  simp [scaleNormal, div_eq_mul_inv, mul_comm]

theorem norm_scaleNormal_le {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) :
    ‖scaleNormal (E := E) h‖ ≤ h⁻¹ := by
  have hi : 1 ≤ h⁻¹ := one_le_inv₀ hh |>.2 hh₁
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hh.le) fun q => ?_
  rw [scaleNormal_apply, Prod.norm_def, max_le_iff]
  constructor
  · exact (norm_fst_le q).trans (le_mul_of_one_le_left (norm_nonneg _) hi)
  · rw [div_eq_mul_inv, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hh.le), mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_snd_le q) (inv_nonneg.mpr hh.le)

theorem norm_iteratedFDeriv_scaleNormal_le {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {U : Set E} (hU : IsOpen U) {f : E × ℝ → F} (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (q : E × ℝ) (hq : q.1 ∈ U) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun p : E × ℝ => f (p.1,p.2 / h)) q‖ ≤
      ‖iteratedFDeriv ℝ j f (q.1,q.2 / h)‖ * (h⁻¹) ^ j := by
  let L : E × ℝ →L[ℝ] E × ℝ := scaleNormal h
  let S : Set (E × ℝ) := U ×ˢ univ
  have hS : IsOpen S := hU.prod isOpen_univ
  have hV : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hq' : q ∈ L ⁻¹' S := by
    change L q ∈ S
    rw [show L q = (q.1,q.2 / h) from scaleNormal_apply h q]
    exact ⟨hq,mem_univ _⟩
  have he := L.iteratedFDerivWithin_comp_right hf hS.uniqueDiffOn hV.uniqueDiffOn hq'
    (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen j hV hq',
    iteratedFDerivWithin_of_isOpen j hS (show L q ∈ S from hq')] at he
  simp_rw [← scaleNormal_apply h]
  change ‖iteratedFDeriv ℝ j (f ∘ L) q‖ ≤ ‖iteratedFDeriv ℝ j f (L q)‖ * h⁻¹ ^ j
  rw [he]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_fin]
  gcongr
  exact norm_scaleNormal_le hh hh₁

end CalderonPaper
