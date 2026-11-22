module

public import Proof.CalderonN.ModelOutputNorms
public import Proof.CalderonN.WeightedOutputConvergence
import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open OAI.AnisotropicCalderon.SphereHarmonic

private theorem integrableOn_local_weighted_norm_sq {Y : Set (X dim)} (hY : IsOpen Y)
    (weight : X dim → ℝ) (hw : ContinuousOn weight Y) (U : X dim → SphereL2 dim)
    (hU : Continuous U) (hc : HasCompactSupport U) (hs : tsupport U ⊆ Y) :
    IntegrableOn (fun y => weight y*‖U y‖^2) Y := by
  have hsupport : tsupport (fun y => ‖U y‖^2) ⊆ tsupport U := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro y hy
    contrapose! hy
    intro hmem
    exact (show ‖U y‖^2 ≠ 0 from hmem) (by simp [image_eq_zero_of_notMem_tsupport hy])
  exact (integrable_local_weighted hY weight _ hw (hU.norm.pow 2)
    (hc.of_isClosed_subset (isClosed_tsupport _) hsupport) (hsupport.trans hs)).integrableOn

namespace AngularComponentData
variable {Y : Set (X dim)} {g : (MetricField dim)} {e : (Frame dim)} {φ : (Field dim)} {E : HarmonicTestExpansion Y g e φ}
  {r : (X dim) → ℝ} {L : ℂ →L[ℝ] ℝ}

lemma raisingOutput_support (Q : AngularComponentData E r L) : tsupport Q.raisingOutput ⊆ E.supportSet := by
  apply closure_minimal _ E.compactSupportSet.isClosed
  intro y hy
  by_contra hn
  exact hy (Q.raisingOutput_zero hn)

lemma loweringOutput_support (Q : AngularComponentData E r L) : tsupport Q.loweringOutput ⊆ E.supportSet := by
  apply closure_minimal _ E.compactSupportSet.isClosed
  intro y hy
  by_contra hn
  exact hy (Q.loweringOutput_zero hn)

lemma integrable_raising_norm_sq (Q : AngularComponentData E r L) (hY : IsOpen Y)
    (weight : (X dim) → ℝ) (hw : ContinuousOn weight Y) : IntegrableOn (fun y => weight y*‖Q.raisingOutput y‖^2) Y :=
  integrableOn_local_weighted_norm_sq hY weight hw Q.raisingOutput Q.contDiff_raisingOutput.continuous
    Q.raisingOutput_compact (Q.raisingOutput_support.trans E.supportSubset)

lemma integrable_lowering_norm_sq (Q : AngularComponentData E r L) (hY : IsOpen Y)
    (weight : (X dim) → ℝ) (hw : ContinuousOn weight Y) : IntegrableOn (fun y => weight y*‖Q.loweringOutput y‖^2) Y :=
  integrableOn_local_weighted_norm_sq hY weight hw Q.loweringOutput Q.contDiff_loweringOutput.continuous
    Q.loweringOutput_compact (Q.loweringOutput_support.trans E.supportSubset)

lemma tendsto_raising_partial_norm_sq (Q : AngularComponentData E r L) (hY : IsOpen Y)
    (weight : (X dim) → ℝ) (hw : ContinuousOn weight Y) (hp : ∀ y ∈ Y,0 ≤ weight y) :
    Tendsto (fun n : ℕ => ∫ y in Y,weight y*‖harmonicPartialSum n (Q.raisingOutput y)‖^2)
      atTop (𝓝 (∫ y in Y,weight y*‖Q.raisingOutput y‖^2)) := by
  have hpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ weight y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact hp y hy
  exact tendsto_integral_weighted_partialSum_norm_sq (volume.restrict Y) weight
    (hw.aestronglyMeasurable hY.measurableSet) hpos Q.raisingOutput Q.contDiff_raisingOutput.continuous.aestronglyMeasurable
    (Q.integrable_raising_norm_sq hY weight hw)

lemma tendsto_lowering_partial_norm_sq (Q : AngularComponentData E r L) (hY : IsOpen Y)
    (weight : (X dim) → ℝ) (hw : ContinuousOn weight Y) (hp : ∀ y ∈ Y,0 ≤ weight y) :
    Tendsto (fun n : ℕ => ∫ y in Y,weight y*‖harmonicPartialSum n (Q.loweringOutput y)‖^2)
      atTop (𝓝 (∫ y in Y,weight y*‖Q.loweringOutput y‖^2)) := by
  have hpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ weight y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact hp y hy
  exact tendsto_integral_weighted_partialSum_norm_sq (volume.restrict Y) weight
    (hw.aestronglyMeasurable hY.measurableSet) hpos Q.loweringOutput Q.contDiff_loweringOutput.continuous.aestronglyMeasurable
    (Q.integrable_lowering_norm_sq hY weight hw)

lemma integrable_raising_partial_norm_sq (Q : AngularComponentData E r L) (hY : IsOpen Y)
    (weight : (X dim) → ℝ) (hw : ContinuousOn weight Y) (hp : ∀ y ∈ Y,0 ≤ weight y) (n : ℕ) :
    IntegrableOn (fun y => weight y*‖harmonicPartialSum n (Q.raisingOutput y)‖^2) Y := by
  have hpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ weight y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact hp y hy
  exact integrable_weighted_partialSum_norm_sq (volume.restrict Y) weight
    (hw.aestronglyMeasurable hY.measurableSet) hpos Q.raisingOutput Q.contDiff_raisingOutput.continuous.aestronglyMeasurable
    (Q.integrable_raising_norm_sq hY weight hw) n

lemma integrable_lowering_partial_norm_sq (Q : AngularComponentData E r L) (hY : IsOpen Y)
    (weight : (X dim) → ℝ) (hw : ContinuousOn weight Y) (hp : ∀ y ∈ Y,0 ≤ weight y) (n : ℕ) :
    IntegrableOn (fun y => weight y*‖harmonicPartialSum n (Q.loweringOutput y)‖^2) Y := by
  have hpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ weight y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact hp y hy
  exact integrable_weighted_partialSum_norm_sq (volume.restrict Y) weight
    (hw.aestronglyMeasurable hY.measurableSet) hpos Q.loweringOutput Q.contDiff_loweringOutput.continuous.aestronglyMeasurable
    (Q.integrable_lowering_norm_sq hY weight hw) n

end AngularComponentData

namespace AngularModelData
variable {Y : Set (X dim)} {g : (MetricField dim)} {e : (Frame dim)} {φ : (Field dim)} {E : HarmonicTestExpansion Y g e φ} {r : (X dim) → ℝ}

def raisingSquare (D : AngularModelData E r) : ℝ :=
  (∫ y in Y,metricDensity g y*‖D.realComponent.raisingOutput y‖^2)+
    (∫ y in Y,metricDensity g y*‖D.imagComponent.raisingOutput y‖^2)

def loweringSquare (D : AngularModelData E r) : ℝ :=
  (∫ y in Y,metricDensity g y*‖D.realComponent.loweringOutput y‖^2)+
    (∫ y in Y,metricDensity g y*‖D.imagComponent.loweringOutput y‖^2)

lemma outputSq_finiteRaised_eq_integrals (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) :
    outputSq Y g e (finiteRaisedField g e (Finset.range n) id E.basis E.realCoefficients E.imagCoefficients
      (fun x => Real.log (r x))) =
      (∫ y in Y,metricDensity g y*‖harmonicPartialSum (n+2) (D.realComponent.raisingOutput y)‖^2)+
        (∫ y in Y,metricDensity g y*‖harmonicPartialSum (n+2) (D.imagComponent.raisingOutput y)‖^2) := by
  have hρ := (h.contDiffOn_density hK).continuousOn
  have hp : ∀ y ∈ Y,0 ≤ metricDensity g y := fun y _ => Real.sqrt_nonneg _
  rw [← integral_add (D.realComponent.integrable_raising_partial_norm_sq hY _ hρ hp (n+2))
    (D.imagComponent.integrable_raising_partial_norm_sq hY _ hρ hp (n+2))]
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  change metricDensity g y*fiberSq e y _ = _
  rw [D.fiberSq_finiteRaised_eq_partial hY h hK he hframe hφ n hy,mul_add]

lemma outputSq_finiteLowered_eq_integrals (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (n : ℕ) :
    outputSq Y g e (finiteLoweredField g e (Finset.range n) id E.basis E.realCoefficients E.imagCoefficients
      (fun x => Real.log (r x))) =
      (∫ y in Y,metricDensity g y*‖harmonicPartialSum n (D.realComponent.loweringOutput y)‖^2)+
        (∫ y in Y,metricDensity g y*‖harmonicPartialSum n (D.imagComponent.loweringOutput y)‖^2) := by
  have hρ := (h.contDiffOn_density hK).continuousOn
  have hp : ∀ y ∈ Y,0 ≤ metricDensity g y := fun y _ => Real.sqrt_nonneg _
  rw [← integral_add (D.realComponent.integrable_lowering_partial_norm_sq hY _ hρ hp n)
    (D.imagComponent.integrable_lowering_partial_norm_sq hY _ hρ hp n)]
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  change metricDensity g y*fiberSq e y _ = _
  rw [D.fiberSq_finiteLowered_eq_partial hY h hK he hframe hφ n hy,mul_add]

/-- The actual finite polynomial raising outputs converge in square to the smooth graph output. -/
theorem tendsto_outputSq_finiteRaised (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) :
    Tendsto (fun n : ℕ => outputSq Y g e (finiteRaisedField g e (Finset.range n) id E.basis E.realCoefficients E.imagCoefficients
      (fun x => Real.log (r x)))) atTop (𝓝 D.raisingSquare) := by
  have hρ := (h.contDiffOn_density hK).continuousOn
  have hp : ∀ y ∈ Y,0 ≤ metricDensity g y := fun y _ => Real.sqrt_nonneg _
  have hr := (D.realComponent.tendsto_raising_partial_norm_sq hY _ hρ hp).comp (tendsto_add_atTop_nat 2)
  have hi := (D.imagComponent.tendsto_raising_partial_norm_sq hY _ hρ hp).comp (tendsto_add_atTop_nat 2)
  have hEq : (fun n : ℕ => outputSq Y g e (finiteRaisedField g e (Finset.range n) id E.basis E.realCoefficients E.imagCoefficients
      (fun x => Real.log (r x)))) =
      (fun n => (∫ y in Y,metricDensity g y*‖harmonicPartialSum (n+2) (D.realComponent.raisingOutput y)‖^2)+
        (∫ y in Y,metricDensity g y*‖harmonicPartialSum (n+2) (D.imagComponent.raisingOutput y)‖^2)) :=
    funext (fun n => D.outputSq_finiteRaised_eq_integrals hY h hK he hframe hφ n)
  rw [hEq]
  exact hr.add hi

theorem tendsto_outputSq_finiteLowered (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) :
    Tendsto (fun n : ℕ => outputSq Y g e (finiteLoweredField g e (Finset.range n) id E.basis E.realCoefficients E.imagCoefficients
      (fun x => Real.log (r x)))) atTop (𝓝 D.loweringSquare) := by
  have hρ := (h.contDiffOn_density hK).continuousOn
  have hp : ∀ y ∈ Y,0 ≤ metricDensity g y := fun y _ => Real.sqrt_nonneg _
  have hr := D.realComponent.tendsto_lowering_partial_norm_sq hY _ hρ hp
  have hi := D.imagComponent.tendsto_lowering_partial_norm_sq hY _ hρ hp
  have hEq : (fun n : ℕ => outputSq Y g e (finiteLoweredField g e (Finset.range n) id E.basis E.realCoefficients E.imagCoefficients
      (fun x => Real.log (r x)))) =
      (fun n => (∫ y in Y,metricDensity g y*‖harmonicPartialSum n (D.realComponent.loweringOutput y)‖^2)+
        (∫ y in Y,metricDensity g y*‖harmonicPartialSum n (D.imagComponent.loweringOutput y)‖^2)) :=
    funext (fun n => D.outputSq_finiteLowered_eq_integrals hY h hK he hframe hφ n)
  rw [hEq]
  exact hr.add hi

end AngularModelData
end CalderonN
