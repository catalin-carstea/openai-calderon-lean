module

public import Proof.CalderonN.Moments
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! The polar integration argument is adapted from
`Proof/Archive/ActualRadialDivergencePolarIntegration.lean`,
`ActualRadialDivergenceFubini.lean` and `ActualBallDivergenceFlux.lean`
in Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. -/

@[expose] public section

noncomputable section
open MeasureTheory Metric Set
open scoped InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev chartSurfaceMeasure (dim : ℕ) : Measure ↥(sphere (0 : (X dim)) 1) := (volume : Measure (X dim)).toSphere

/-- The outward flux of a chart vector density on the unit sphere. -/
@[expose] def unitSphereFlux (W : (X dim) → (X dim)) : ℝ :=
  ∫ w : ↥(sphere (0 : (X dim)) 1), ⟪(w : (X dim)),W w⟫_ℝ ∂(chartSurfaceMeasure dim)

theorem integral_eq_sphere_radial_product (f : (X dim) → ℝ) :
    (∫ x : (X dim), f x) =
      ∫ z : ↥(sphere (0 : (X dim)) 1) × Ioi (0 : ℝ), f (z.2.val • z.1.val)
        ∂(chartSurfaceMeasure dim).prod (Measure.volumeIoiPow (dim-1)) := by
  let e := homeomorphUnitSphereProd (X dim)
  have hmp := (volume : Measure (X dim)).measurePreserving_homeomorphUnitSphereProd
  have he : Module.finrank ℝ (X dim) - 1 = dim-1 := by simp [finrank_euclideanSpace]
  calc
    (∫ x : (X dim), f x) =
        ∫ x : ({(0 : (X dim))}ᶜ : Set (X dim)), f x.val ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      have h := hmp.integral_comp (Homeomorph.measurableEmbedding _)
        (fun z => f (e.symm z).val)
      simpa only [e, Homeomorph.symm_apply_apply, he, chartSurfaceMeasure,
        homeomorphUnitSphereProd_symm_apply_coe] using h

 

theorem integrable_sphere_radial_product (f : (X dim) → ℝ)
    (hf : Integrable f (volume : Measure (X dim))) :
    Integrable (fun z : ↥(sphere (0 : (X dim)) 1) × Ioi (0 : ℝ) => f (z.2.val • z.1.val))
      ((chartSurfaceMeasure dim).prod (Measure.volumeIoiPow (dim-1))) := by
  let g : ↥(sphere (0 : (X dim)) 1) × Ioi (0 : ℝ) → ℝ := fun z => f (z.2.val • z.1.val)
  have hmp := (volume : Measure (X dim)).measurePreserving_homeomorphUnitSphereProd
  have he : Module.finrank ℝ (X dim) - 1 = dim-1 := by simp [finrank_euclideanSpace]
  have hg : g ∘ homeomorphUnitSphereProd (X dim) = f ∘ Subtype.val := by
    funext x
    have hx : ‖(x : (X dim))‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
    simp only [g,Function.comp_apply,homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe,smul_inv_smul₀ hx]
  change Integrable g ((volume : Measure (X dim)).toSphere.prod (Measure.volumeIoiPow (dim-1)))
  rw [← he, ← hmp.integrable_comp_emb (homeomorphUnitSphereProd (X dim)).measurableEmbedding,
    hg, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
  exact hf.integrableOn

theorem integral_volumeIoiPow_chart (dim : ℕ) (h : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), h r.val ∂Measure.volumeIoiPow (dim-1)) =
      ∫ r in Ioi (0 : ℝ), r^(dim-1) * h r := by
  have hm : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val^(dim-1))) := by
    fun_prop
  have ht : ∀ᵐ r : Ioi (0 : ℝ) ∂(volume.comap Subtype.val),
      ENNReal.ofReal (r.val^(dim-1)) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul hm ht]
  have he : ∀ r : Ioi (0 : ℝ), (ENNReal.ofReal (r.val^(dim-1))).toReal = r.val^(dim-1) :=
    fun r => ENNReal.toReal_ofReal (pow_nonneg r.property.le _)
  simp only [he, smul_eq_mul]
  exact integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r^(dim-1) * h r)

theorem integral_eq_integral_Ioi_surface (f : (X dim) → ℝ)
    (hf : Integrable f (volume : Measure (X dim))) :
    (∫ x : (X dim), f x) = ∫ r in Ioi (0 : ℝ), r^(dim-1) *
      ∫ w : ↥(sphere (0 : (X dim)) 1), f (r • w.val) ∂(chartSurfaceMeasure dim) := by
  rw [integral_eq_sphere_radial_product,
    integral_prod_symm _ (integrable_sphere_radial_product f hf)]
  exact integral_volumeIoiPow_chart dim
    (fun r : ℝ => ∫ w : ↥(sphere (0 : (X dim)) 1), f (r • w.val) ∂(chartSurfaceMeasure dim))

theorem integral_ball_zero_eq_radial_interval (f : (X dim) → ℝ) (R : ℝ) (hR : 0 < R)
    (hf : IntegrableOn f (ball (0 : (X dim)) R) (volume : Measure (X dim))) :
    (∫ x in ball (0 : (X dim)) R, f x) = ∫ r in (0 : ℝ)..R, r^(dim-1) *
      ∫ w : ↥(sphere (0 : (X dim)) 1), f (r • w.val) ∂(chartSurfaceMeasure dim) := by
  have hint : Integrable ((ball (0 : (X dim)) R).indicator f) (volume : Measure (X dim)) :=
    hf.integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball, integral_eq_integral_Ioi_surface _ hint]
  have hinner : ∀ r ∈ Ioi (0 : ℝ), r^(dim-1) *
      (∫ w : ↥(sphere (0 : (X dim)) 1), (ball (0 : (X dim)) R).indicator f (r • w.val) ∂(chartSurfaceMeasure dim)) =
        (Iio R).indicator (fun r : ℝ => r^(dim-1) *
          ∫ w : ↥(sphere (0 : (X dim)) 1), f (r • w.val) ∂(chartSurfaceMeasure dim)) r := by
    intro r hr
    have hmem (w : ↥(sphere (0 : (X dim)) 1)) : r • w.val ∈ ball (0 : (X dim)) R ↔ r < R := by
      rw [mem_ball_zero_iff, norm_smul, (mem_sphere_zero_iff_norm.mp w.property), mul_one,
        Real.norm_of_nonneg hr.le]
    by_cases hrR : r < R
    · rw [indicator_of_mem (mem_Iio.mpr hrR)]
      simp_rw [indicator_of_mem ((hmem _).mpr hrR)]
    · rw [indicator_of_notMem (by simpa using hrR)]
      simp_rw [indicator_of_notMem ((not_congr (hmem _)).mpr hrR)]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]

end CalderonN
