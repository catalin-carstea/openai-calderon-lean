module

public import Proof.Manuscript.RadiusAngularAnnularBounds
public import Proof.Manuscript.RadiusOperatorTaylor

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

theorem hasDerivAt_radiusFirstAngular_line
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} (hU : IsOpen U) {D : Set E} (hD : IsOpen D)
    {a : P × E → E → V} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ D))
    (q : Q) (r : ℝ) (hq : e (q,r) ∈ U) (x : E) {ξ : E} (hξ : ξ ∈ D) :
    HasDerivAt (fun s => a (e (q,s),x) ξ) (radiusFirstAngular e a (e (q,r),x) ξ) r := by
  let O := radiusAngularDomain e U D
  have hO : IsOpen O :=
    ((hU.prod hD).prod isOpen_univ).preimage (radiusLastAnnulusEquiv e).continuous
  have hqO : (((q,ξ),x),r) ∈ O := ⟨⟨hq,hξ⟩,mem_univ _⟩
  have hF := hasDerivAt_radialFirstDerivative
    ((radiusAngularLift_contDiffOn (e := e) ha).contDiffAt (hO.mem_nhds hqO))
  simpa only [radiusAngularLift,radiusFirstAngular,LinearIsometryEquiv.symm_apply_apply] using hF

theorem radiusAngular_taylor_eq [CompleteSpace V]
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} (hU : IsOpen U) {D : Set E} (hD : IsOpen D)
    {a : P × E → E → V} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ D))
    (q : Q) (r : ℝ) (hq : ∀ t ∈ Icc (0:ℝ) 1, e (q,t*r) ∈ U)
    (x : E) {ξ : E} (hξ : ξ ∈ D) :
    a (e (q,r),x) ξ = a (e (q,0),x) ξ + r • radiusFirstAngular e a (e (q,0),x) ξ +
      r^2 • radiusTaylorAngular e a (e (q,r),x) ξ := by
  let O := radiusAngularDomain e U D
  have hO : IsOpen O :=
    ((hU.prod hD).prod isOpen_univ).preimage (radiusLastAnnulusEquiv e).continuous
  have hqO : (((q,ξ),x),r) ∈ radiusSegment O := fun t ht => ⟨⟨hq t ht,hξ⟩,mem_univ _⟩
  have hF := radius_taylor_eq hO (radiusAngularLift_contDiffOn (e := e) ha) hqO
  simpa only [radiusAngularLift,radiusFirstAngular,radiusTaylorAngular,
    LinearIsometryEquiv.symm_apply_apply] using hF

end CalderonPaper
