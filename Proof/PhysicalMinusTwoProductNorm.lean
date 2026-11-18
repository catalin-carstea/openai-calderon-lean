import Proof.ProductFibreNormIdentity
import Proof.WeightedPartialDifferenceNormConvergence
import Proof.PhysicalOutputRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual product-space norm after subtracting two realized outputs
is the physical fibre norm of the same difference. This is the norm bridge
for the retained principal trace after its two genuine complements. -/
theorem PhysicalOutputRealization.norm_sub_two_product_outputs
    {Y : Set X} (hY : IsOpen Y) {g : MetricField} {e : Frame} {F : Field}
    (hρ : ContinuousOn (metricDensity g) Y) (P : PhysicalOutputRealization Y g e F)
    {U1 V1 U2 V2 : X → SphereL2} {S1 S2 : Set X}
    (A : ProductOutputRealization U1 V1 Y g S1) (B : ProductOutputRealization U2 V2 Y g S2)
    (W Z : X → SphereL2)
    (hRe : ∀ y ∈ Y,W y =ᵐ[sphereProbability] (fun v => (P.representative (y,v)).re))
    (hIm : ∀ y ∈ Y,Z y =ᵐ[sphereProbability] (fun v => (P.representative (y,v)).im))
    (hW : AEStronglyMeasurable W (volume.restrict Y))
    (hZ : AEStronglyMeasurable Z (volume.restrict Y))
    (hSR : AEStronglyMeasurable (fun y => U1 y+U2 y) (volume.restrict Y))
    (hSI : AEStronglyMeasurable (fun y => V1 y+V2 y) (volume.restrict Y))
    (hiW : IntegrableOn (fun y => metricDensity g y*‖W y‖^2) Y)
    (hiZ : IntegrableOn (fun y => metricDensity g y*‖Z y‖^2) Y)
    (hiSR : IntegrableOn (fun y => metricDensity g y*‖U1 y+U2 y‖^2) Y)
    (hiSI : IntegrableOn (fun y => metricDensity g y*‖V1 y+V2 y‖^2) Y) :
    ‖P.output-A.output-B.output‖^2=
      (∫ y in Y,metricDensity g y*‖W y-(U1 y+U2 y)‖^2)+
        (∫ y in Y,metricDensity g y*‖Z y-(V1 y+V2 y)‖^2) := by
  let qn := fun n => A.approximation.approximation n+B.approximation.approximation n
  let Gn := fun n (z : X × UnitSphere) => A.approximation.sphere.field n z+B.approximation.sphere.field n z
  have hQAE (n : ℕ) : qn n =ᵐ[(outputBaseMeasure Y g).prod sphereProbability] Gn n := by
    filter_upwards [Lp.coeFn_add (A.approximation.approximation n) (B.approximation.approximation n),
      A.approximation.partialAE n,B.approximation.partialAE n] with z hz ha hb
    simp only [Pi.add_apply] at hz
    exact hz.trans (congrArg₂ (fun a b : ℂ => a+b) ha hb)
  have hGnRe (n : ℕ) (y : X) : harmonicPartialSum n (U1 y+U2 y) =ᵐ[sphereProbability]
      (fun v => (Gn n (y,v)).re) := by
    rw [map_add]
    filter_upwards [Lp.coeFn_add (harmonicPartialSum n (U1 y)) (harmonicPartialSum n (U2 y)),
      A.approximation.sphere.realAE n y,B.approximation.sphere.realAE n y] with v hv ha hb
    simp only [Pi.add_apply] at hv
    change _=(A.approximation.sphere.field n (y,v)+B.approximation.sphere.field n (y,v)).re
    rw [Complex.add_re]
    exact hv.trans (congrArg₂ (fun a b : ℝ => a+b) ha hb)
  have hGnIm (n : ℕ) (y : X) : harmonicPartialSum n (V1 y+V2 y) =ᵐ[sphereProbability]
      (fun v => (Gn n (y,v)).im) := by
    rw [map_add]
    filter_upwards [Lp.coeFn_add (harmonicPartialSum n (V1 y)) (harmonicPartialSum n (V2 y)),
      A.approximation.sphere.imagAE n y,B.approximation.sphere.imagAE n y] with v hv ha hb
    simp only [Pi.add_apply] at hv
    change _=(A.approximation.sphere.field n (y,v)+B.approximation.sphere.field n (y,v)).im
    rw [Complex.add_im]
    exact hv.trans (congrArg₂ (fun a b : ℝ => a+b) ha hb)
  have hμ := hρ.aestronglyMeasurable (μ:=volume) hY.measurableSet
  have hμ0 : ∀ᵐ y ∂volume.restrict Y,0 ≤ metricDensity g y := Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
  have hEq (n : ℕ) : ‖P.output-qn n‖^2=
      (∫ y in Y,metricDensity g y*‖W y-harmonicPartialSum n (U1 y+U2 y)‖^2)+
        (∫ y in Y,metricDensity g y*‖Z y-harmonicPartialSum n (V1 y+V2 y)‖^2) := by
    have hh := norm_product_output_sub_of_fibre_components hY hρ P.output (qn n)
      P.representative (Gn n) P.memLp.coeFn_toLp (hQAE n) W Z
      (fun y => harmonicPartialSum n (U1 y+U2 y)) (fun y => harmonicPartialSum n (V1 y+V2 y))
      hRe hIm (fun y _ => hGnRe n y) (fun y _ => hGnIm n y)
    rw [hh]
    simp only [mul_add]
    exact integral_add
      (integrable_weighted_sub_partialSum_norm_sq (volume.restrict Y) _ hμ hμ0 W _ hW hSR hiW hiSR n)
      (integrable_weighted_sub_partialSum_norm_sq (volume.restrict Y) _ hμ hμ0 Z _ hZ hSI hiZ hiSI n)
  have hReal := tendsto_integral_weighted_sub_partialSum_norm_sq (volume.restrict Y) _ hμ hμ0 W _ hW hSR hiW hiSR
  have hImag := tendsto_integral_weighted_sub_partialSum_norm_sq (volume.restrict Y) _ hμ hμ0 Z _ hZ hSI hiZ hiSI
  have hOut : Tendsto (fun n => ‖P.output-qn n‖^2) atTop (𝓝 (‖P.output-(A.output+B.output)‖^2)) :=
    (tendsto_const_nhds.sub (A.converges.add B.converges)).norm.pow 2
  have hLim := tendsto_nhds_unique hOut ((hReal.add hImag).congr'
    (Eventually.of_forall (fun n => (hEq n).symm)))
  simpa only [sub_sub] using hLim

end ShrinkingSpheres
