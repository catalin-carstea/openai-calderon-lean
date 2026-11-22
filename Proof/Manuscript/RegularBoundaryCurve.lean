module

public import Proof.Manuscript.Lemma81Defs
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem real_clm_isInvertible_of_at_one_ne_zero {L : ℝ →L[ℝ] ℝ} (hnz : L 1 ≠ 0) :
    L.IsInvertible := by
  have hL (x : ℝ) : L x = x * L 1 := by
    simpa only [smul_eq_mul, mul_one] using L.map_smul x (1 : ℝ)
  let K : ℝ →L[ℝ] ℝ := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := K)
  · apply ContinuousLinearMap.ext
    intro x
    change L ((L 1)⁻¹ * x) = x
    rw [hL]
    field_simp
  · apply ContinuousLinearMap.ext
    intro x
    change (L 1)⁻¹ * L x = x
    rw [hL x, mul_comm x, ← mul_assoc, inv_mul_cancel₀ hnz, one_mul]

/-- A tangent vector to a regular level set is the initial velocity of a
smooth curve in that level set. -/
theorem exists_curve_in_regular_level {ρ : E → ℝ} {p v w : E}
    (hρ : ContDiffAt ℝ ∞ ρ p) (hw : fderiv ℝ ρ p w ≠ 0)
    (hv : fderiv ℝ ρ p v = 0) :
    ∃ c : ℝ → E, c 0 = p ∧ ContDiffAt ℝ ∞ c 0 ∧ HasDerivAt c v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), ρ (c t) = ρ p := by
  let A : (ℝ × ℝ) →L[ℝ] E :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v).coprod
      ((ContinuousLinearMap.id ℝ ℝ).smulRight w)
  let f (u : ℝ × ℝ) := ρ (p + A u)
  have hA : HasFDerivAt (fun u => p + A u) A (0 : ℝ × ℝ) :=
    A.hasFDerivAt.const_add p
  have hf : ContDiffAt ℝ ∞ f (0 : ℝ × ℝ) := by
    have hp : ContDiffAt ℝ ∞ ρ (p + A (0 : ℝ × ℝ)) := by simpa
    exact hp.comp 0 (contDiff_const.add A.contDiff).contDiffAt
  have hd : fderiv ℝ f (0 : ℝ × ℝ) = fderiv ℝ ρ p ∘L A := by
    have hp : HasFDerivAt ρ (fderiv ℝ ρ p) (p + A (0 : ℝ × ℝ)) := by
      simpa using (hρ.differentiableAt (by simp)).hasFDerivAt
    exact (hp.comp 0 hA).fderiv
  have hright : (fderiv ℝ f (0 : ℝ × ℝ) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply real_clm_isInvertible_of_at_one_ne_zero
    simpa [hd, A] using hw
  let φ := hf.implicitFunction (by simp) hright
  have hφ₀ : φ 0 = 0 := hf.implicitFunction_apply_self (by simp) hright
  have hs : ContDiffAt ℝ ∞ φ 0 := hf.contDiffAt_implicitFunction (by simp) hright
  have hφ' : HasDerivAt φ 0 0 := by
    have h := (hf.hasStrictFDerivAt_implicitFunction (by simp) hright).hasFDerivAt.hasDerivAt
    convert h using 1
    simp [hd, A, hv]
  let c (t : ℝ) := p + A (t, φ t)
  have hc₀ : c 0 = p := by simp [c, hφ₀, A]
  have hc : ContDiffAt ℝ ∞ c 0 :=
    contDiffAt_const.add (A.contDiff.contDiffAt.comp 0 (contDiffAt_id.prodMk hs))
  have hc' : HasDerivAt c v 0 := by
    have h := A.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).prodMk hφ')
    simpa [c, A, Function.comp_def] using h.const_add p
  refine ⟨c, hc₀, hc, hc', ?_⟩
  simpa [f, c] using hf.eventually_apply_implicitFunction (by simp) hright

/-- Positive directional derivative enters the positive side of the level set. -/
theorem eventually_line_pos {ρ : E → ℝ} {p w : E} (hρ : DifferentiableAt ℝ ρ p)
    (hvalue : ρ p = 0) (hw : 0 < fderiv ℝ ρ p w) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < ρ (p + t • w) := by
  have hline : HasDerivAt (fun t : ℝ => p + t • w) w 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add p)
  have hf : HasDerivAt (fun t : ℝ => ρ (p + t • w)) (fderiv ℝ ρ p w) 0 := by
    have h := hρ.hasFDerivAt
    simpa [Function.comp_def] using h.comp_hasDerivAt_of_eq 0 hline (by simp)
  filter_upwards [hf.tendsto_slope_zero_right (Ioi_mem_nhds hw), self_mem_nhdsWithin]
    with t ht hs
  have hpos : 0 < t := hs
  have hprod : 0 < t⁻¹ * ρ (p + t • w) := by
    simpa [slope, hvalue, smul_eq_mul] using ht
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hpos)).mp hprod

theorem frontier_of_defining_function_zero {Ω U : Set E} {ρ : E → ℝ} {p w : E}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hp : p ∈ U)
    (hρ : DifferentiableAt ℝ ρ p) (hb : ∀ x ∈ U, x ∈ Ω ↔ 0 < ρ x)
    (hp₀ : ρ p = 0) (hpos : 0 < fderiv ℝ ρ p w) : p ∈ frontier Ω := by
  have hline : Tendsto (fun t : ℝ => p + t • w) (𝓝 (0 : ℝ)) (𝓝 p) := by
    have h : ContinuousAt (fun t : ℝ => p + t • w) 0 := by fun_prop
    simpa using h.tendsto
  have hwithin := hline.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hOmega : ∀ᶠ t in 𝓝[>] (0 : ℝ), p + t • w ∈ Ω := by
    filter_upwards [hwithin (hU.mem_nhds hp), eventually_line_pos hρ hp₀ hpos] with t ht hρt
    exact (hb _ ht).mpr hρt
  have hclosure := mem_closure_of_tendsto hwithin hOmega
  exact ⟨hclosure, by simp [hΩ.interior_eq, hb _ hp, hp₀]⟩

theorem exists_tangent_boundary_curve {Ω U : Set E} {ρ : E → ℝ} {p v w : E}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hp : p ∈ U)
    (hρ : ContDiffOn ℝ ∞ ρ U) (hb : ∀ x ∈ U, x ∈ Ω ↔ 0 < ρ x)
    (hp₀ : ρ p = 0) (hw : 0 < fderiv ℝ ρ p w) (hv : fderiv ℝ ρ p v = 0) :
    ∃ c : ℝ → E, c 0 = p ∧ ContDiffAt ℝ ∞ c 0 ∧ HasDerivAt c v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U ∩ frontier Ω := by
  have hr := hρ.contDiffAt (hU.mem_nhds hp)
  obtain ⟨c, hc₀, hc, hdc, hcz⟩ := exists_curve_in_regular_level hr hw.ne' hv
  have hct : Tendsto c (𝓝 0) (𝓝 p) := hc₀ ▸ hc.continuousAt.tendsto
  have hcont : ContinuousAt (fun x => fderiv ℝ ρ x w) p :=
    (hr.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  refine ⟨c, hc₀, hc, hdc, ?_⟩
  filter_upwards [hct (hU.mem_nhds hp), hcz, (hcont.tendsto.comp hct) (Ioi_mem_nhds hw)] with
    t ht hz hpos
  exact ⟨ht, frontier_of_defining_function_zero hΩ hU ht
    ((hρ.contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)) hb (hz.trans hp₀) hpos⟩

end CalderonPaper
