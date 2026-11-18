import Proof.ProductPartialRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_sub_sq_le_center {F : Type*} [SeminormedAddCommGroup F] (a b c : F) :
    ‖a-b‖^2 ≤ 2*‖a-c‖^2+2*‖b-c‖^2 := by
  have h : ‖a-b‖ ≤ ‖a-c‖+‖b-c‖ := by
    calc
      _ = ‖(a-c)-(b-c)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  nlinarith [sq_nonneg (‖a-c‖-‖b-c‖)]

lemma cauchySeq_of_square_error {F : Type*} [NormedAddCommGroup F] (u : ℕ → F) (error : ℕ → ℝ)
    (hlim : Tendsto error atTop (𝓝 0))
    (hbound : ∀ n m,‖u n-u m‖^2 ≤ 2*error n+2*error m) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hp : 0 < ε^2/4 := by positivity
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hp))
  refine ⟨N,fun n hn m hm => ?_⟩
  rw [dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
  have hn' := hN n hn
  have hm' := hN m hm
  have hb := hbound n m
  nlinarith

namespace ProductPartialRealization
variable {U V : X → SphereL2} {Y : Set X} {g : MetricField} {S : Set X}

lemma cauchy (A : ProductPartialRealization U V Y g S) (hY : IsOpen Y)
    (hρ : ContinuousOn (metricDensity g) Y) (hU : Continuous U) (hV : Continuous V)
    (hiU : IntegrableOn (fun y => metricDensity g y*‖U y‖^2) Y)
    (hiV : IntegrableOn (fun y => metricDensity g y*‖V y‖^2) Y) : CauchySeq A.approximation := by
  have hw : AEStronglyMeasurable (metricDensity g) (volume.restrict Y) := hρ.aestronglyMeasurable hY.measurableSet
  have hwpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ metricDensity g y := Eventually.of_forall (fun y => Real.sqrt_nonneg _)
  let eu (n : ℕ) (y : X) := metricDensity g y*‖harmonicPartialSum n (U y)-U y‖^2
  let ev (n : ℕ) (y : X) := metricDensity g y*‖harmonicPartialSum n (V y)-V y‖^2
  have hiu (n : ℕ) : IntegrableOn (eu n) Y := integrable_weighted_harmonicPartialSum_sub _ _ hw hwpos U hU.aestronglyMeasurable hiU n
  have hiv (n : ℕ) : IntegrableOn (ev n) Y := integrable_weighted_harmonicPartialSum_sub _ _ hw hwpos V hV.aestronglyMeasurable hiV n
  have hlu := tendsto_integral_weighted_harmonicPartialSum (volume.restrict Y) _ hw hwpos U hU.aestronglyMeasurable hiU
  have hlv := tendsto_integral_weighted_harmonicPartialSum (volume.restrict Y) _ hw hwpos V hV.aestronglyMeasurable hiV
  apply cauchySeq_of_square_error A.approximation (fun n => (∫ y in Y,eu n y)+(∫ y in Y,ev n y))
    (by simpa only [add_zero] using hlu.add hlv)
  intro n m
  rw [A.differenceNormSq]
  have hupper := ((((hiu n).const_mul 2).add ((hiu m).const_mul 2)).add ((hiv n).const_mul 2)).add ((hiv m).const_mul 2)
  have hbound : (∫ y in Y,metricDensity g y*(‖harmonicPartialSum n (U y)-harmonicPartialSum m (U y)‖^2+
      ‖harmonicPartialSum n (V y)-harmonicPartialSum m (V y)‖^2)) ≤
      ∫ y in Y,2*eu n y+2*eu m y+2*ev n y+2*ev m y := by
    apply integral_mono_of_nonneg (Eventually.of_forall (fun y => mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))) hupper
    apply Eventually.of_forall
    intro y
    have hu := norm_sub_sq_le_center (harmonicPartialSum n (U y)) (harmonicPartialSum m (U y)) (U y)
    have hv := norm_sub_sq_le_center (harmonicPartialSum n (V y)) (harmonicPartialSum m (V y)) (V y)
    simp only [Pi.add_apply]
    dsimp only [eu,ev]
    have hsum := mul_le_mul_of_nonneg_left (add_le_add hu hv) (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _)
    dsimp only [metricDensity] at hsum ⊢
    nlinarith only [hsum]
  have h2 : IntegrableOn (fun y => 2*eu n y+2*eu m y) Y := ((hiu n).const_mul 2).add ((hiu m).const_mul 2)
  have h3 : IntegrableOn (fun y => 2*eu n y+2*eu m y+2*ev n y) Y := h2.add ((hiv n).const_mul 2)
  rw [integral_add h3 ((hiv m).const_mul 2),integral_add h2 ((hiv n).const_mul 2),
    integral_add ((hiu n).const_mul 2) ((hiu m).const_mul 2)] at hbound
  simp only [integral_const_mul] at hbound
  linarith

end ProductPartialRealization


structure ProductOutputRealization (U V : X → SphereL2) (Y : Set X) (g : MetricField) (S : Set X) where
  approximation : ProductPartialRealization U V Y g S
  output : Lp ℂ 2 ((outputBaseMeasure Y g).prod sphereProbability)
  converges : Tendsto approximation.approximation atTop (𝓝 output)
  normSq : ‖output‖^2 = (∫ y in Y,metricDensity g y*‖U y‖^2)+(∫ y in Y,metricDensity g y*‖V y‖^2)

/-- Smooth compact Hilbert-valued angular sections have genuine outputs in the physical
    product measure, constructed as limits of their finite harmonic representatives. -/
theorem exists_productOutputRealization {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hρ : ContinuousOn (metricDensity g) Y) (U V : X → SphereL2)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hzeroU : ∀ y ∉ S,U y = 0) (hzeroV : ∀ y ∉ S,V y = 0) :
    Nonempty (ProductOutputRealization U V Y g S) := by
  obtain ⟨A⟩ := exists_productPartialRealization hY hρ U V hU hV S hS hSY hzeroU hzeroV
  have hscU : tsupport U ⊆ S := closure_minimal (fun y hy => by_contra fun hn => hy (hzeroU y hn)) hS.isClosed
  have hscV : tsupport V ⊆ S := closure_minimal (fun y hy => by_contra fun hn => hy (hzeroV y hn)) hS.isClosed
  have hiU := integrableOn_local_weighted_norm_sq hY _ hρ U hU.continuous (HasCompactSupport.intro hS hzeroU) (hscU.trans hSY)
  have hiV := integrableOn_local_weighted_norm_sq hY _ hρ V hV.continuous (HasCompactSupport.intro hS hzeroV) (hscV.trans hSY)
  obtain ⟨T,hT⟩ := cauchySeq_tendsto_of_complete (A.cauchy hY hρ hU.continuous hV.continuous hiU hiV)
  refine ⟨⟨A,T,hT,?_⟩⟩
  have hw : AEStronglyMeasurable (metricDensity g) (volume.restrict Y) := hρ.aestronglyMeasurable hY.measurableSet
  have hwpos : ∀ᵐ y ∂volume.restrict Y,0 ≤ metricDensity g y := Eventually.of_forall (fun y => Real.sqrt_nonneg _)
  have hlu := tendsto_integral_weighted_partialSum_norm_sq (volume.restrict Y) _ hw hwpos U hU.continuous.aestronglyMeasurable hiU
  have hlv := tendsto_integral_weighted_partialSum_norm_sq (volume.restrict Y) _ hw hwpos V hV.continuous.aestronglyMeasurable hiV
  have heq (n : ℕ) : ‖A.approximation n‖^2 =
      (∫ y in Y,metricDensity g y*‖harmonicPartialSum n (U y)‖^2)+
        (∫ y in Y,metricDensity g y*‖harmonicPartialSum n (V y)‖^2) := by
    rw [A.normSq]
    simp_rw [mul_add]
    exact integral_add
      (integrable_weighted_partialSum_norm_sq _ _ hw hwpos U hU.continuous.aestronglyMeasurable hiU n)
      (integrable_weighted_partialSum_norm_sq _ _ hw hwpos V hV.continuous.aestronglyMeasurable hiV n)
  exact tendsto_nhds_unique (hT.norm.pow 2) ((hlu.add hlv).congr' (Eventually.of_forall (fun n => (heq n).symm)))

end ShrinkingSpheres
