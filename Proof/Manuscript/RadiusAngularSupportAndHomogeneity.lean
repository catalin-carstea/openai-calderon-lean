module

public import Proof.Manuscript.RadiusAngularLine
public import Proof.Manuscript.GeometryAngularSupport

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter MeasureTheory Set
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

variable {P Q E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem radiusFirstAngular_homogeneousAngularCoefficient
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} (hU : IsOpen U)
    {b : ℕ → P × E → E → V} {D : Set E} (hD : IsOpen D) (k : ℕ)
    (hb : ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (hH : ContDiffOn ℝ ∞ (Function.uncurry (homogeneousAngularCoefficient b k))
      ((U ×ˢ univ) ×ˢ ({0}ᶜ : Set E)))
    {p : P} (hp : p ∈ U) (x : E) {ξ : E} (hξ : ξ ≠ 0)
    (hν : ‖ξ‖⁻¹ • ξ ∈ D) :
    radiusFirstAngular e (homogeneousAngularCoefficient b k) (p,x) ξ =
      homogeneousAngularCoefficient (fun k => radiusFirstAngular e (b k)) k (p,x) ξ := by
  let q := (e.symm p).1
  let r := (e.symm p).2
  have hpr : e (q,r) = p := e.apply_symm_apply _
  have h₁ := hasDerivAt_radiusFirstAngular_line hU isClosed_singleton.isOpen_compl hH q r
    (hpr.symm ▸ hp) x (show ξ ∈ ({0}ᶜ : Set E) from hξ)
  have h₂ := hasDerivAt_radiusFirstAngular_line hU hD hb q r (hpr.symm ▸ hp) x hν
  have h₃ := HasDerivAt.const_smul (angularSymbolScale k ‖ξ‖) h₂
  have h := h₁.unique (show HasDerivAt
    (fun s => homogeneousAngularCoefficient b k (e (q,s),x) ξ)
    (angularSymbolScale k ‖ξ‖ • radiusFirstAngular e (b k) (e (q,r),x) (‖ξ‖⁻¹ • ξ)) r from h₃)
  rw [hpr] at h
  exact h

private theorem angularLift_zero_germ {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {S : Set E}
    (hS : IsClosed S) {a : P × E → E → V} (ha : ∀ p x, x ∉ S → ∀ ξ, a (p,x) ξ = 0)
    {z : ((Q × E) × E) × ℝ} (hz : z.1.2 ∉ S) :
    radiusAngularLift e a =ᶠ[𝓝 z] fun _ => 0 := by
  have hProj : Continuous (fun w : ((Q × E) × E) × ℝ => w.1.2) :=
    continuous_snd.comp continuous_fst
  filter_upwards [hProj.continuousAt.eventually (hS.isOpen_compl.mem_nhds hz)] with q hq
  exact ha _ q.1.2 hq _

theorem radiusFirstAngular_zero_off_support {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {S : Set E}
    (hS : IsClosed S) {a : P × E → E → V} (ha : ∀ p x, x ∉ S → ∀ ξ, a (p,x) ξ = 0)
    (p : P) (x : E) (hx : x ∉ S) (ξ : E) :
    radiusFirstAngular e a (p,x) ξ = 0 := by
  let z := ((((e.symm p).1,ξ),x),(e.symm p).2)
  have he := (angularLift_zero_germ (e := e) hS ha (z := z) hx).fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (radiusAngularLift e a) z (0,1) = 0
  simp only [he,fderiv_fun_const,Pi.zero_apply,zero_apply]

theorem radiusTaylorAngular_zero_off_support {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {S : Set E}
    (hS : IsClosed S) {a : P × E → E → V} (ha : ∀ p x, x ∉ S → ∀ ξ, a (p,x) ξ = 0)
    (p : P) (x : E) (hx : x ∉ S) (ξ : E) :
    radiusTaylorAngular e a (p,x) ξ = 0 := by
  let z := ((((e.symm p).1,ξ),x),(e.symm p).2)
  have hZ (w : ((Q × E) × E) × ℝ) (hw : w.1.2 ∉ S) :
      radialFirstDerivative (radiusAngularLift e a) w = 0 := by
    have he := (angularLift_zero_germ (e := e) hS ha (z := w) hw).fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (radiusAngularLift e a) w (0,1) = 0
    simp only [he,fderiv_fun_const,Pi.zero_apply,zero_apply]
  have hSecond (t : ℝ) : radiusSecondDerivative (radiusAngularLift e a) (z.1,t*z.2) = 0 := by
    let w := (z.1,t*z.2)
    have hProj : Continuous (fun w : ((Q × E) × E) × ℝ => w.1.2) :=
      continuous_snd.comp continuous_fst
    have he : radialFirstDerivative (radiusAngularLift e a) =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hProj.continuousAt.eventually (hS.isOpen_compl.mem_nhds
        (show w.1.2 ∉ S from hx))] with w' hw'
      exact hZ w' hw'
    change fderiv ℝ (radialFirstDerivative (radiusAngularLift e a)) w (0,1) = 0
    simp only [he.fderiv_eq,fderiv_fun_const,Pi.zero_apply,zero_apply]
  change (∫ t in (0:ℝ)..1, (1-t) • radiusSecondDerivative (radiusAngularLift e a) (z.1,t*z.2)) = 0
  simp [hSecond]

end CalderonPaper
