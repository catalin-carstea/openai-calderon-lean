import Proof.Absorption
import Proof.ComplexPolynomial
import Proof.MetricDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The base measure in the actual output space. -/
def outputBaseMeasure (Y : Set X) (g : MetricField) : Measure X :=
  (volume.restrict Y).withDensity (fun y => ENNReal.ofReal (metricDensity g y))

instance outputBaseMeasure_sfinite (Y : Set X) (g : MetricField) : SFinite (outputBaseMeasure Y g) := by
  unfold outputBaseMeasure
  infer_instance

lemma outputMeasure_eq_base (Y : Set X) (d : Data) :
    outputMeasure Y d = (outputBaseMeasure Y d.γ).prod sphereProbability := rfl

lemma integrable_outputBase_iff {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hρ : ContinuousOn (metricDensity g) Y) (f : X → ℝ) :
    Integrable f (outputBaseMeasure Y g) ↔ IntegrableOn (fun y => metricDensity g y*f y) Y := by
  have hm : AEStronglyMeasurable (metricDensity g) (volume.restrict Y) := hρ.aestronglyMeasurable hY.measurableSet
  unfold outputBaseMeasure
  rw [integrable_withDensity_iff_integrable_smul₀' hm.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))]
  simp only [metricDensity,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),smul_eq_mul]
  rfl

lemma integral_outputBase {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hρ : ContinuousOn (metricDensity g) Y) (f : X → ℝ) :
    (∫ y,f y ∂outputBaseMeasure Y g) = ∫ y in Y,metricDensity g y*f y := by
  unfold outputBaseMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hρ.aestronglyMeasurable hY.measurableSet).aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))]
  simp only [metricDensity,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),smul_eq_mul]

/-- Fubini realizes every continuous standard-sphere field with finite weighted square
    as an element of the very product L² space used in the frozen analytic estimates. -/
lemma memLp_output_product {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hρ : ContinuousOn (metricDensity g) Y) (G : X × UnitSphere → ℂ) (hG : Continuous G)
    (hmass : IntegrableOn (fun y => metricDensity g y*(∫ v,‖G (y,v)‖^2 ∂sphereProbability)) Y) :
    MemLp G 2 ((outputBaseMeasure Y g).prod sphereProbability) := by
  apply (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hG.norm.pow 2).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun y => ?_),?_⟩
  · exact (((hG.comp (continuous_const.prodMk continuous_id)).norm).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · have hi := (integrable_outputBase_iff hY hρ (fun y => ∫ v,‖G (y,v)‖^2 ∂sphereProbability)).mpr hmass
    simpa only [Pi.pow_apply,Real.norm_eq_abs,abs_pow,abs_norm] using hi

lemma norm_sq_output_product {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hρ : ContinuousOn (metricDensity g) Y) (G : X × UnitSphere → ℂ)
    (hG : MemLp G 2 ((outputBaseMeasure Y g).prod sphereProbability)) :
    ‖hG.toLp G‖^2 = ∫ y in Y,metricDensity g y*(∫ v,‖G (y,v)‖^2 ∂sphereProbability) := by
  calc
    _ = ∫ z,‖(hG.toLp G) z‖^2 ∂((outputBaseMeasure Y g).prod sphereProbability) := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    _ = ∫ z,‖G z‖^2 ∂((outputBaseMeasure Y g).prod sphereProbability) := by
      apply integral_congr_ae
      filter_upwards [hG.coeFn_toLp] with z hz
      rw [hz]
    _ = ∫ y,(∫ v,‖G (y,v)‖^2 ∂sphereProbability) ∂outputBaseMeasure Y g :=
      integral_prod _ ((memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG)
    _ = _ := integral_outputBase hY hρ _

end ShrinkingSpheres
