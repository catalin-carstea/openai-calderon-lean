import Proof.ProductFibreNormIdentity
import Proof.SpherePartialRealization
import Proof.BesselTruncationConvergence
import Proof.WeightedOutputConvergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

structure ProductPartialRealization (U V : X → SphereL2) (Y : Set X) (g : MetricField) (S : Set X) where
  sphere : SpherePartialRealization U V S
  approximation : ℕ → Lp ℂ 2 ((outputBaseMeasure Y g).prod sphereProbability)
  partialAE : ∀ n,approximation n =ᵐ[(outputBaseMeasure Y g).prod sphereProbability] sphere.field n
  normSq : ∀ n,‖approximation n‖^2 = ∫ y in Y,metricDensity g y*
    (‖harmonicPartialSum n (U y)‖^2+‖harmonicPartialSum n (V y)‖^2)
  differenceNormSq : ∀ n m,‖approximation n-approximation m‖^2 = ∫ y in Y,metricDensity g y*
    (‖harmonicPartialSum n (U y)-harmonicPartialSum m (U y)‖^2+
      ‖harmonicPartialSum n (V y)-harmonicPartialSum m (V y)‖^2)

theorem exists_productPartialRealization {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hρ : ContinuousOn (metricDensity g) Y) (U V : X → SphereL2)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hzeroU : ∀ y ∉ S,U y = 0) (hzeroV : ∀ y ∉ S,V y = 0) :
    Nonempty (ProductPartialRealization U V Y g S) := by
  obtain ⟨A⟩ := exists_spherePartialRealization U V hU hV S hS hzeroU hzeroV
  have hscU : tsupport U ⊆ S := closure_minimal (fun y hy => by_contra fun hn => hy (hzeroU y hn)) hS.isClosed
  have hscV : tsupport V ⊆ S := closure_minimal (fun y hy => by_contra fun hn => hy (hzeroV y hn)) hS.isClosed
  have hiU := integrableOn_local_weighted_norm_sq hY _ hρ U hU.continuous (HasCompactSupport.intro hS hzeroU) (hscU.trans hSY)
  have hiV := integrableOn_local_weighted_norm_sq hY _ hρ V hV.continuous (HasCompactSupport.intro hS hzeroV) (hscV.trans hSY)
  have hw : AEStronglyMeasurable (metricDensity g) (volume.restrict Y) := hρ.aestronglyMeasurable hY.measurableSet
  have hwpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ metricDensity g y := Eventually.of_forall (fun y => Real.sqrt_nonneg _)
  have hpU (n : ℕ) := integrable_weighted_partialSum_norm_sq (volume.restrict Y) _ hw hwpos U hU.continuous.aestronglyMeasurable hiU n
  have hpV (n : ℕ) := integrable_weighted_partialSum_norm_sq (volume.restrict Y) _ hw hwpos V hV.continuous.aestronglyMeasurable hiV n
  have hm (n : ℕ) : MemLp (A.field n) 2 ((outputBaseMeasure Y g).prod sphereProbability) := by
    apply memLp_output_product hY hρ _ (A.continuous n)
    have hi := (hpU n).add (hpV n)
    apply hi.congr
    filter_upwards [] with y
    rw [A.fiber_square]
    exact (mul_add (metricDensity g y) _ _).symm
  refine ⟨⟨A,fun n => (hm n).toLp (A.field n),fun n => (hm n).coeFn_toLp,?_,?_⟩⟩
  · intro n
    exact norm_product_output_of_fibre_components hY hρ ((hm n).toLp (A.field n))
      (A.field n) (hm n).coeFn_toLp (fun y => harmonicPartialSum n (U y))
      (fun y => harmonicPartialSum n (V y)) (fun y _ => A.realAE n y) (fun y _ => A.imagAE n y)
  · intro n m
    exact norm_product_output_sub_of_fibre_components hY hρ
      ((hm n).toLp (A.field n)) ((hm m).toLp (A.field m))
      (A.field n) (A.field m) (hm n).coeFn_toLp (hm m).coeFn_toLp
      (fun y => harmonicPartialSum n (U y)) (fun y => harmonicPartialSum n (V y))
      (fun y => harmonicPartialSum m (U y)) (fun y => harmonicPartialSum m (V y))
      (fun y _ => A.realAE n y) (fun y _ => A.imagAE n y)
      (fun y _ => A.realAE m y) (fun y _ => A.imagAE m y)

end ShrinkingSpheres
