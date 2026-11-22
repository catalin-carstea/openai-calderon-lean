module

public import Proof.Manuscript.Lemma81Defs
import Proof.Manuscript.BoundaryOrientation
import Proof.Manuscript.ConformalDifferentiation
import Proof.Manuscript.LocalExtensions
import Proof.Manuscript.RegularBoundaryCurve
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {n : ℕ}
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

private theorem exists_nonzero_tangent (hn : 3 ≤ n) (L : Eₙ →L[ℝ] ℝ) :
    ∃ v : Eₙ, v ≠ 0 ∧ L v = 0 := by
  by_contra! h
  have hi : Function.Injective L := (injective_iff_map_eq_zero L).mpr
    (fun v hv => by_contra fun hne => h v hne hv)
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := L.toLinearMap) hi
  simp at hdim
  omega

theorem local_conformal_of_extensions {Ω U : Set Eₙ} {F G : Eₙ → Eₙ} {b B : Eₙ → ℝ}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hG : EqOn G F (U ∩ closure Ω))
    (hB : EqOn B b (U ∩ closure Ω)) (hc : EuclideanConformalOn Ω F b) :
    EuclideanConformalOn (U ∩ Ω) G B := by
  intro x hx v w
  have h := (SmoothThrough.eventuallyEq_extension hU hΩ hx hG).fderiv_eq (𝕜 := ℝ)
  simpa only [h, hB ⟨hx.1, subset_closure hx.2⟩] using hc x hx.2 v w

private theorem conformal_extends_to_frontier {Ω U : Set Eₙ} {G : Eₙ → Eₙ} {B : Eₙ → ℝ}
    {p : Eₙ} (hU : IsOpen U) (hp : p ∈ U) (hpΩ : p ∈ closure Ω)
    (hG : ContDiffAt ℝ ∞ G p) (hB : ContinuousAt B p)
    (hc : EuclideanConformalOn (U ∩ Ω) G B) (v w : Eₙ) :
    inner ℝ (fderiv ℝ G p v) (fderiv ℝ G p w) = Real.exp (2 * B p) * inner ℝ v w := by
  have d := hG.continuousAt_fderiv (by simp)
  have hleft : ContinuousAt (fun x => inner ℝ (fderiv ℝ G x v) (fderiv ℝ G x w)) p :=
    (d.clm_apply continuousAt_const).inner (d.clm_apply continuousAt_const)
  have hright : ContinuousAt (fun x => Real.exp (2 * B x) * inner ℝ v w) p := by fun_prop
  exact eq_at_closure_of_eqOn_local hU hp hpΩ hleft hright (fun x hx => hc x hx v w)

private theorem right_deriv_nonneg_of_eventually_pos {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (h₀ : f 0 = 0) (hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f t) :
    0 ≤ a := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [hpos, self_mem_nhdsWithin] with t hft ht
  change 0 < t at ht
  simpa [h₀, smul_eq_mul] using (mul_pos (inv_pos.mpr ht) hft).le

private theorem boundary_normal_side {Ω U V : Set Eₙ} {ρ : Eₙ → ℝ} {F G : Eₙ → Eₙ}
    {p ν : Eₙ} (hU : IsOpen U) (hV : IsOpen V) (hpU : p ∈ U) (hpV : p ∈ V)
    (hρ : DifferentiableAt ℝ ρ p) (hρ₀ : ρ p = 0)
    (hregion : ∀ x ∈ V, x ∈ Ω ↔ 0 < ρ x)
    (hν : 0 < fderiv ℝ ρ p ν) (hG : DifferentiableAt ℝ G p) (hGp : G p = p)
    (hEq : EqOn G F (U ∩ closure Ω)) (hFG : MapsTo F Ω Ω) :
    0 ≤ fderiv ℝ ρ p (fderiv ℝ G p ν) := by
  let c (t : ℝ) := p + t • ν
  have hc₀ : c 0 = p := by simp [c]
  have hc : HasDerivAt c ν 0 := by
    simpa [c] using (((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add p)
  have hdg := hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc hc₀.symm
  have hd := hρ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hdg (by simp [hc₀, hGp])
  apply right_deriv_nonneg_of_eventually_pos hd (by simp [Function.comp_def, hGp, hc₀, hρ₀])
  have hct : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    rw [← hc₀]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hgt : Tendsto (G ∘ c) (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    rw [← hGp]
    exact hG.continuousAt.tendsto.comp hct
  filter_upwards [hct (hU.mem_nhds hpU), hct (hV.mem_nhds hpV),
    hgt (hV.mem_nhds hpV), eventually_line_pos hρ hρ₀ hν] with t htU htV htG ht
  have hctΩ : c t ∈ Ω := (hregion _ htV).mpr ht
  have hGtΩ : G (c t) ∈ Ω := by
    rw [hEq ⟨htU, subset_closure hctΩ⟩]
    exact hFG hctΩ
  exact (hregion _ htG).mp hGtΩ

theorem conformal_boundary_first_jet (hn : 3 ≤ n) {Ω U : Set Eₙ}
    (hΩ : IsOpen Ω) (hboundary : HasSmoothEuclideanBoundary Ω)
    {F G : Eₙ → Eₙ} {b B : Eₙ → ℝ} (hFG : MapsTo F Ω Ω)
    {Γ : Set (frontier Ω)} (hΓ : IsOpen Γ)
    (hfix : ∀ p : frontier Ω, p ∈ Γ → F p = (p : Eₙ))
    (hconf : EuclideanConformalOn Ω F b) (hU : IsOpen U)
    (p : frontier Ω) (hpΓ : p ∈ Γ) (hpU : (p : Eₙ) ∈ U)
    (hG : ContDiffOn ℝ ∞ G U) (hB : ContDiffOn ℝ ∞ B U)
    (hEqG : EqOn G F (U ∩ closure Ω)) (hEqB : EqOn B b (U ∩ closure Ω)) :
    fderiv ℝ G (p : Eₙ) = ContinuousLinearMap.id ℝ Eₙ ∧ B p = 0 := by
  have hpΩ : (p : Eₙ) ∈ closure Ω := p.property.1
  have hG₀ : G p = (p : Eₙ) := (hEqG ⟨hpU, hpΩ⟩).trans (hfix p hpΓ)
  obtain ⟨V, hV, hpV, ρ, hρ, hρ₀, hρnz, hregion⟩ := hboundary (p : Eₙ) p.property
  obtain ⟨P, hP, hPg⟩ := isOpen_induced_iff.mp hΓ
  have hpP : (p : Eₙ) ∈ P := by
    change p ∈ Subtype.val ⁻¹' P
    rwa [hPg]
  let L := fderiv ℝ ρ (p : Eₙ)
  let ν : Eₙ := (InnerProductSpace.toDual ℝ Eₙ).symm L
  let T := fderiv ℝ G (p : Eₙ)
  have hν (v : Eₙ) : L v = inner ℝ ν v :=
    (congrArg (fun A : Eₙ →L[ℝ] ℝ => A v)
      ((InnerProductSpace.toDual ℝ Eₙ).apply_symm_apply L)).symm
  have hνnz : ν ≠ 0 := by
    intro hz
    apply hρnz
    apply ContinuousLinearMap.ext
    intro v
    simp [← show L = fderiv ℝ ρ (p : Eₙ) by rfl, hν v, hz]
  have hνpos : 0 < L ν := by
    rw [hν]
    exact real_inner_self_pos.mpr hνnz
  have hT (v : Eₙ) (hv : L v = 0) : T v = v := by
    obtain ⟨c, hc₀, hc, hd, hcV⟩ := exists_tangent_boundary_curve hΩ hV hpV hρ
      hregion hρ₀ hνpos hv
    have hct : Tendsto c (𝓝 0) (𝓝 (p : Eₙ)) := by
      simpa only [hc₀] using hc.continuousAt.tendsto
    have heq : G ∘ c =ᶠ[𝓝 0] c := by
      filter_upwards [hcV, hct (hU.mem_nhds hpU), hct (hP.mem_nhds hpP)] with t htV htU htP
      let pt : frontier Ω := ⟨c t, htV.2⟩
      have htΓ : pt ∈ Γ := by
        rw [← hPg]
        exact htP
      exact (hEqG ⟨htU, htV.2.1⟩).trans (hfix pt htΓ)
    have hg := (hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
    have hdc := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd hc₀.symm
    exact (hdc.congr_of_eventuallyEq heq.symm).unique hd
  have hconf' := local_conformal_of_extensions hΩ hU hEqG hEqB hconf
  have hscaled := conformal_extends_to_frontier hU hpU hpΩ
    (hG.contDiffAt (hU.mem_nhds hpU)) ((hB.contDiffAt (hU.mem_nhds hpU)).continuousAt) hconf'
  obtain ⟨v, hv, hvL⟩ := exists_nonzero_tangent hn L
  have hc := hscaled v v
  change inner ℝ (T v) (T v) = _ at hc
  rw [hT v hvL] at hc
  have hvpos := real_inner_self_pos.mpr hv
  have hexp : Real.exp (2 * B p) = 1 := by
    apply mul_right_cancel₀ hvpos.ne'
    simpa only [one_mul] using hc.symm
  have hb₀ : B p = 0 := by
    have := Real.exp_injective (hexp.trans Real.exp_zero.symm)
    linarith
  have horth (v w : Eₙ) : inner ℝ (T v) (T w) = inner ℝ v w := by
    simpa only [hexp, one_mul] using hscaled v w
  have hside : 0 ≤ L (T ν) :=
    boundary_normal_side hU hV hpU hpV ((hρ.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp))
      hρ₀ hregion hνpos ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)) hG₀ hEqG hFG
  exact ⟨orthogonal_eq_id_of_fixes_tangent T L ν hν hνpos hT horth hside, hb₀⟩

theorem conformal_boundary_exponent_derivative (hn : 3 ≤ n) {Ω U : Set Eₙ}
    (hΩ : IsOpen Ω) (hboundary : HasSmoothEuclideanBoundary Ω)
    {F G : Eₙ → Eₙ} {b B : Eₙ → ℝ} (hFG : MapsTo F Ω Ω)
    {Γ : Set (frontier Ω)} (hΓ : IsOpen Γ)
    (hfix : ∀ p : frontier Ω, p ∈ Γ → F p = (p : Eₙ))
    (hconf : EuclideanConformalOn Ω F b) (hU : IsOpen U)
    (p : frontier Ω) (hpΓ : p ∈ Γ) (hpU : (p : Eₙ) ∈ U)
    (hG : ContDiffOn ℝ ∞ G U) (hB : ContDiffOn ℝ ∞ B U)
    (hEqG : EqOn G F (U ∩ closure Ω)) (hEqB : EqOn B b (U ∩ closure Ω)) :
    fderiv ℝ B (p : Eₙ) = 0 := by
  have hpΩ : (p : Eₙ) ∈ closure Ω := p.property.1
  obtain ⟨V, hV, hpV, ρ, hρ, hρ₀, hρnz, hregion⟩ := hboundary (p : Eₙ) p.property
  let L := fderiv ℝ ρ (p : Eₙ)
  obtain ⟨v, hvnz, hvtan⟩ := exists_nonzero_tangent hn L
  have hexists : ∃ ν, 0 < L ν := by
    by_contra! h
    apply hρnz
    apply ContinuousLinearMap.ext
    intro w
    change L w = 0
    have ha := h w
    have hb := h (-w)
    rw [map_neg] at hb
    linarith
  obtain ⟨ν, hν⟩ := hexists
  obtain ⟨c, hc₀, hc, hd, hcV⟩ := exists_tangent_boundary_curve hΩ hV hpV hρ
    hregion hρ₀ hν hvtan
  obtain ⟨P, hP, hPg⟩ := isOpen_induced_iff.mp hΓ
  have hpP : (p : Eₙ) ∈ P := by
    change p ∈ Subtype.val ⁻¹' P
    rwa [hPg]
  have hct : Tendsto c (𝓝 0) (𝓝 (p : Eₙ)) := by
    simpa only [hc₀] using hc.continuousAt.tendsto
  have heq : (fderiv ℝ G ∘ c) =ᶠ[𝓝 0] (fun _ => ContinuousLinearMap.id ℝ Eₙ) := by
    filter_upwards [hcV, hct (hU.mem_nhds hpU), hct (hP.mem_nhds hpP)] with t htV htU htP
    let pt : frontier Ω := ⟨c t, htV.2⟩
    have htΓ : pt ∈ Γ := by
      rw [← hPg]
      exact htP
    exact (conformal_boundary_first_jet hn hΩ hboundary hFG hΓ hfix hconf hU pt htΓ htU
      hG hB hEqG hEqB).1
  have hGₚ := hG.contDiffAt (hU.mem_nhds hpU)
  have hBₚ := hB.contDiffAt (hU.mem_nhds hpU)
  have hDf : DifferentiableAt ℝ (fderiv ℝ G) (p : Eₙ) :=
    (hGₚ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hderiv := hDf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd hc₀.symm
  have hDzero := (hderiv.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const _ _)
  have hh (w : Eₙ) : directional v (directional w G) (p : Eₙ) = 0 := by
    change (fderiv ℝ (fun x => fderiv ℝ G x w) (p : Eₙ)) v = 0
    rw [fderiv_clm_apply hDf (differentiableAt_const w)]
    simp [hDzero]
  have hlocal := local_conformal_of_extensions hΩ hU hEqG hEqB hconf
  have hcone (w : Eₙ) :
      inner ℝ (directional w (directional v G) (p : Eₙ)) (directional v G (p : Eₙ)) +
          inner ℝ (directional v G (p : Eₙ)) (directional w (directional v G) (p : Eₙ)) =
        (2 * directional w B (p : Eₙ)) * Real.exp (2 * B p) * inner ℝ v v := by
    have hD₁ := (directional_contDiffAt (v := v) hGₚ).continuousAt
    have hD₂ := (directional_contDiffAt (v := w) (directional_contDiffAt (v := v) hGₚ)).continuousAt
    have hDb := (directional_contDiffAt (v := w) hBₚ).continuousAt
    have hBc := hBₚ.continuousAt
    have hleft : ContinuousAt (fun x : Eₙ =>
        inner ℝ (directional w (directional v G) x) (directional v G x) +
          inner ℝ (directional v G x) (directional w (directional v G) x)) (p : Eₙ) :=
      (hD₂.inner hD₁).add (hD₁.inner hD₂)
    have hright : ContinuousAt (fun x : Eₙ =>
        (2 * directional w B x) * Real.exp (2 * B x) * inner ℝ v v) (p : Eₙ) := by fun_prop
    refine eq_at_closure_of_eqOn_local hU hpU hpΩ hleft hright ?_
    intro x hx
    exact conformal_differentiated (hU.inter hΩ) hx (hG.contDiffAt (hU.mem_nhds hx.1))
      (hB.contDiffAt (hU.mem_nhds hx.1)) hlocal w v v
  apply ContinuousLinearMap.ext
  intro w
  have h := hcone w
  rw [directional_comm hGₚ w v, hh w, inner_zero_left, inner_zero_right,
    add_zero] at h
  have hinner := real_inner_self_pos.mpr hvnz
  have hexp := Real.exp_pos (2 * B p)
  have hwzero : directional w B (p : Eₙ) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hinner.ne')).resolve_right hexp.ne'
  exact hwzero

end CalderonPaper
