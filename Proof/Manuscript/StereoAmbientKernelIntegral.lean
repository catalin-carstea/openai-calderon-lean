module

public import Proof.Manuscript.StereoAmbientKernel
public import Proof.Manuscript.StereoSphereMeasure

import Mathlib.Tactic

public section

noncomputable section

open Set Metric MeasureTheory CalderonN
open scoped ContDiff ENNReal

namespace CalderonPaper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The reciprocal chart density in the extended kernel exactly converts
its normalized sphere integral back to its Euclidean chart integral. -/
theorem exists_joint_smooth_stereographic_kernel_integral
    {dim : ℕ} [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {V : Set P} (v : ↥(standardSphere dim)) {χ η : X dim → ℂ}
    (hχ : smoothNear χ (standardSphere dim)) (hη : smoothNear η (standardSphere dim))
    (hχS : angularSupport χ ⊆ (stereographic' (dim-1) v).source)
    (hηS : angularSupport η ⊆ (stereographic' (dim-1) v).source)
    {d : AngularCoordinates dim → ℝ} (hd : ContDiff ℝ ∞ d) (hd₀ : ∀ z, 0 < d z)
    (hDensity : Measure.map (stereographic' (dim-1) v)
      ((sphereProbability dim).restrict (stereographic' (dim-1) v).source) =
      (volume : Measure (AngularCoordinates dim)).withDensity (fun x => ENNReal.ofReal (d x)))
    {K : P × (AngularCoordinates dim × AngularCoordinates dim) → ℂ}
    (hK : ContDiffOn ℝ ∞ K (V ×ˢ univ)) :
    ∃ F : P × (X dim × X dim) → ℂ, ContDiffOn ℝ ∞ F (V ×ˢ univ) ∧
      ∀ p ∈ V, ∀ w : ↥(standardSphere dim), ∀ u : ↥(standardSphere dim) → ℂ, Continuous u →
        (∫ z, F (p,(w,z)) * u z ∂sphereProbability dim) =
          ∫ x, χ w * η ((stereographic' (dim-1) v).symm x) *
            K (p,(stereographic' (dim-1) v w,x)) * u ((stereographic' (dim-1) v).symm x) := by
  obtain ⟨F,hF,hFs⟩ := exists_joint_smooth_stereographic_cutoff_kernel v hχ hη hχS hηS hd hd₀ hK
  refine ⟨F,hF,?_⟩
  let κ := stereographic' (dim-1) v
  have hv : η v = 0 := by
    by_contra hv
    have hmem : v ∈ κ.source := hηS (subset_closure hv)
    have hSrc : κ.source = {v}ᶜ := stereographic'_source (n := dim-1) v
    rw [hSrc] at hmem
    exact hmem (mem_singleton _)
  intro p hp w u hu
  let f (z : ↥(standardSphere dim)) := F (p,(w,z)) * u z
  have hFz : ContDiff ℝ ∞ (fun z : X dim => F (p,((w : X dim),z))) := by
    apply contDiffOn_univ.mp
    exact hF.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun _ _ => ⟨hp,mem_univ _⟩)
  have hf : Continuous f := (hFz.continuous.comp continuous_subtype_val).mul hu
  have hfv : f v = 0 := by
    change F (p,(w,v)) * u v = 0
    rw [hFs]
    simp [hv]
  change (∫ z, f z ∂sphereProbability dim) = _
  rw [stereographic_sphereProbability_integral_of_supported_density v hd.continuous
    (fun x => (hd₀ x).le) hDensity f hf hfv]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hTarget : κ.target = univ := stereographic'_target (n := dim-1) v
  have hx : x ∈ κ.target := hTarget.symm ▸ mem_univ _
  have hdx : (d x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hd₀ x).ne'
  change (d x : ℂ) * (F (p,(w,κ.symm x)) * u (κ.symm x)) = _
  rw [hFs, show stereographic' (dim-1) v (κ.symm x) = x from κ.right_inv hx]
  field_simp
  simp only [κ]
  ac_rfl

end CalderonPaper
