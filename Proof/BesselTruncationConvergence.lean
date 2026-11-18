import Proof.HarmonicTruncation
import Proof.LocalWeightedIntegration

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 10
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SmoothSphereFields

lemma norm_harmonicPartialSum_sub_le (n : ℕ) (u : SphereL2) :
    ‖harmonicPartialSum n u-u‖ ≤ 2*‖u‖ := by
  calc
    _ ≤ ‖harmonicPartialSum n u‖+‖u‖ := norm_sub_le _ _
    _ ≤ ‖u‖+‖u‖ := add_le_add (norm_harmonicPartialSum_le n u) le_rfl
    _ = _ := by ring

lemma integrable_weighted_harmonicPartialSum_sub {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (weight : A → ℝ) (hw : AEStronglyMeasurable weight μ)
    (hwpos : ∀ᵐ x ∂μ,0 ≤ weight x) (U : A → SphereL2) (hU : AEStronglyMeasurable U μ)
    (hint : Integrable (fun x => weight x*‖U x‖^2) μ) (n : ℕ) :
    Integrable (fun x => weight x*‖harmonicPartialSum n (U x)-U x‖^2) μ := by
  apply (hint.const_mul 4).mono'
    (hw.mul ((((harmonicPartialSum n).continuous.comp_aestronglyMeasurable hU).sub hU).norm.pow 2))
  filter_upwards [hwpos] with x hx
  change ‖weight x*‖harmonicPartialSum n (U x)-U x‖^2‖ ≤ 4*(weight x*‖U x‖^2)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (sq_nonneg _))]
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_harmonicPartialSum_sub_le n (U x))
  nlinarith [mul_le_mul_of_nonneg_left hs hx]

lemma sphereBesselGraph_partialSum_sub (s : ℝ) (u b : SphereL2)
    (hb : (u,b) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s) (n : ℕ) :
    (harmonicPartialSum n u-u,harmonicPartialSum n b-b) ∈
      sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s :=
  (sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s).sub_mem
    (spectralGraph_partialSum orthogonalSphereHarmonics denseSphereHarmonics (besselWeight s) (u,b) hb n) hb

lemma harmonicTruncation_sub_sobolevSq (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ : Field) (U V B C : SphereL2)
    (hRe : U =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).re))
    (hIm : V =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).im))
    (s : ℝ) (hB : (U,B) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hC : (V,C) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s) (n : ℕ) :
    sobolevSq g e s y (fun w => harmonicTruncation g e φ n (y,w)-φ (y,w)) =
      ‖harmonicPartialSum n B-B‖^2+‖harmonicPartialSum n C-C‖^2 := by
  obtain ⟨hnRe,hnIm⟩ := harmonicTruncation_components g e y hframe φ U V hRe hIm n
  have hr : harmonicPartialSum n U-U =ᵐ[sphereProbability]
      (fun v : UnitSphere => (harmonicTruncation g e φ n (y,frameVector e y v.val)-φ (y,frameVector e y v.val)).re) := by
    exact (Lp.coeFn_sub (harmonicPartialSum n U) U).trans (hnRe.sub hRe)
  have hi : harmonicPartialSum n V-V =ᵐ[sphereProbability]
      (fun v : UnitSphere => (harmonicTruncation g e φ n (y,frameVector e y v.val)-φ (y,frameVector e y v.val)).im) := by
    exact (Lp.coeFn_sub (harmonicPartialSum n V) V).trans (hnIm.sub hIm)
  exact sobolevSq_eq_bessel_components g e y hframe _ _ _ _ _ hr hi s
    (sphereBesselGraph_partialSum_sub s U B hB n) (sphereBesselGraph_partialSum_sub s V C hC n)

/-- Weighted Sobolev convergence for the actual finite sums of frozen Legendre kernels.
    All graph outputs, integrability and real/imaginary representatives are explicit. -/
theorem tendsto_integral_sobolev_harmonicTruncation {Y : Set X} (hY : IsOpen Y)
    (g : MetricField) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ : Field) (U V B C : X → SphereL2)
    (hRe : ∀ y ∈ Y,U y =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).re))
    (hIm : ∀ y ∈ Y,V y =ᵐ[sphereProbability] (fun v : UnitSphere => (φ (y,frameVector e y v.val)).im))
    (s : ℝ) (hB : ∀ y ∈ Y,(U y,B y) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (hC : ∀ y ∈ Y,(V y,C y) ∈ sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics s)
    (weight : X → ℝ) (hw : AEStronglyMeasurable weight (volume.restrict Y))
    (hwpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ weight y)
    (hBm : AEStronglyMeasurable B (volume.restrict Y)) (hCm : AEStronglyMeasurable C (volume.restrict Y))
    (hiB : IntegrableOn (fun y => weight y*‖B y‖^2) Y)
    (hiC : IntegrableOn (fun y => weight y*‖C y‖^2) Y) :
    Tendsto (fun n : ℕ => ∫ y in Y,weight y*sobolevSq g e s y
      (fun w => harmonicTruncation g e φ n (y,w)-φ (y,w))) atTop (𝓝 0) := by
  have hlimB := tendsto_integral_weighted_harmonicPartialSum (volume.restrict Y) weight hw hwpos B hBm hiB
  have hlimC := tendsto_integral_weighted_harmonicPartialSum (volume.restrict Y) weight hw hwpos C hCm hiC
  have heq : (fun n : ℕ => ∫ y in Y,weight y*sobolevSq g e s y
      (fun w => harmonicTruncation g e φ n (y,w)-φ (y,w))) =
      (fun n : ℕ => (∫ y in Y,weight y*‖harmonicPartialSum n (B y)-B y‖^2)+
        (∫ y in Y,weight y*‖harmonicPartialSum n (C y)-C y‖^2)) := by
    funext n
    rw [← integral_add (integrable_weighted_harmonicPartialSum_sub (volume.restrict Y) weight hw hwpos B hBm hiB n)
      (integrable_weighted_harmonicPartialSum_sub (volume.restrict Y) weight hw hwpos C hCm hiC n)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [harmonicTruncation_sub_sobolevSq g e y (hframe y hy) φ (U y) (V y) (B y) (C y)
      (hRe y hy) (hIm y hy) s (hB y hy) (hC y hy) n,mul_add]
  rw [heq]
  simpa only [add_zero] using hlimB.add hlimC

lemma integrableOn_local_weighted_norm_sq {E : Type*} [NormedAddCommGroup E]
    {Y : Set X} (hY : IsOpen Y) (weight : X → ℝ) (hw : ContinuousOn weight Y)
    (U : X → E) (hU : Continuous U) (hcomp : HasCompactSupport U) (hsupp : tsupport U ⊆ Y) :
    IntegrableOn (fun y => weight y*‖U y‖^2) Y := by
  have hzero (y : X) (hy : y ∉ tsupport U) : ‖U y‖^2 = 0 := by
    simp only [image_eq_zero_of_notMem_tsupport hy,norm_zero,zero_pow (by omega : 2 ≠ 0)]
  have hsupport : tsupport (fun y => ‖U y‖^2) ⊆ tsupport U := by
    apply closure_minimal _ (isClosed_tsupport U)
    intro y hy
    by_contra hn
    exact hy (hzero y hn)
  exact (integrable_local_weighted hY weight _ hw (hU.norm.pow 2)
    (HasCompactSupport.intro hcomp hzero) (hsupport.trans hsupp)).restrict

/-- Actual smooth compact tests converge under literal Legendre truncation in every angular
    Sobolev norm used by the proposition, with any locally continuous nonnegative base weight. -/
theorem Test.tendsto_weighted_sobolev_harmonicTruncation {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) (s : ℝ) (hs : s ≤ 2)
    (weight : X → ℝ) (hw : ContinuousOn weight Y) (hwpos : ∀ y ∈ Y,0 ≤ weight y) :
    Tendsto (fun n : ℕ => ∫ y in Y,weight y*sobolevSq g e s y
      (fun w => harmonicTruncation g e φ n (y,w)-φ (y,w))) atTop (𝓝 0) := by
  obtain ⟨K,hK,hKY,G,hG,hrep,hzero⟩ := hφ.exists_smooth_standard_representative hY e he hframe
  obtain ⟨U,V,B,C,hU,hV,hB,hC,hcompB,hcompC,hsB,hsC,hRe,hIm,hgraphB,hgraphC⟩ :=
    exists_smooth_bessel_sections G hG K hK hzero s hs
  have hr (y : X) (hy : y ∈ Y) : U y =ᵐ[sphereProbability]
      (fun v : UnitSphere => (φ (y,frameVector e y v.val)).re) := by
    apply (hRe y).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.re (hrep y hy v))
  have hi (y : X) (hy : y ∈ Y) : V y =ᵐ[sphereProbability]
      (fun v : UnitSphere => (φ (y,frameVector e y v.val)).im) := by
    apply (hIm y).trans
    exact Filter.Eventually.of_forall (fun v => congrArg Complex.im (hrep y hy v))
  have hpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ weight y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact hwpos y hy
  exact tendsto_integral_sobolev_harmonicTruncation hY g e hframe φ U V B C hr hi s
    (fun y _ => hgraphB y) (fun y _ => hgraphC y) weight (hw.aestronglyMeasurable hY.measurableSet) hpos
    hB.continuous.aestronglyMeasurable hC.continuous.aestronglyMeasurable
    (integrableOn_local_weighted_norm_sq hY weight hw B hB.continuous hcompB (hsB.trans hKY))
    (integrableOn_local_weighted_norm_sq hY weight hw C hC.continuous hcompC (hsC.trans hKY))

end ShrinkingSpheres
