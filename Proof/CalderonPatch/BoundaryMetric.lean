module

public import Proof.CalderonPatch.BoundaryVolume
public import Proof.CalderonN.Chart

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.MetricPair

public section

noncomputable section
open Bundle Filter Matrix MeasureTheory Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X axis metricPair metricPair_eq_dotProduct vector_eq_sum_axis)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- The frozen coordinate coefficients are smooth up to the flat
boundary of the extended chart. The derivatives here are taken within
the same half space as the measured volume definition. -/
theorem chartMetric_smooth_entries (g : SmoothMetric n M) (p : M) :
    ∀ i j, ContDiffOn ℝ ∞ (fun x => chartMetric g p x i j) (extChartAt J p).target := by
  let e := extChartAt J p
  let _ : RiemannianBundle (fun x : M => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
  have haxis (i : I n) : ContMDiffOn K (ModelWithCorners.tangent J) ∞
      (fun x : X n => (⟨e.symm x, mfderivWithin K J e.symm (range J) x (axis i)⟩ :
        TangentBundle J M)) e.target := by
    let σ : X n → TangentBundle K (X n) := fun x => ⟨x, axis i⟩
    have hσ : ContMDiff K (ModelWithCorners.tangent K) ∞ σ := by
      let d := tangentBundleModelSpaceDiffeomorph K ⊤
      have hpair : ContMDiff K (ModelWithCorners.prod K K) ∞
          (fun x : X n => (x, axis i)) := contMDiff_id.prodMk contMDiff_const
      rw [chartedSpaceSelf_prod] at hpair
      exact d.symm.contMDiff.comp hpair
    have hi : ContMDiffOn K J ∞ e.symm e.target := contMDiffOn_extChartAt_symm (I := J) p
    have hD := hi.contMDiffOn_tangentMapWithin (m := ∞)
      (by simp) (uniqueDiffOn_extChartAt_target (I := J) p).uniqueMDiffOn
    refine (hD.comp hσ.contMDiffOn (fun x hx => hx)).congr ?_
    intro x hx
    change _ = (⟨e.symm x, mfderivWithin K J e.symm e.target x (axis i)⟩ : TangentBundle J M)
    rw [mfderivWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem hx)]
  intro i j
  rw [← contMDiffOn_iff_contDiffOn]
  exact (haxis i).inner_bundle (haxis j)

theorem chartMetric_posDef (g : SmoothMetric n M) (p : M) {x : X n} (hx : x ∈ (extChartAt J p).target) :
    (chartMetric g p x).PosDef := by
  let e := extChartAt J p
  let D : X n →L[ℝ] X n := mfderivWithin K J e.symm (range J) x
  let b : X n →L[ℝ] X n →L[ℝ] ℝ := g.inner (e.symm x)
  have hD : D.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm (I := J) hx
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    change star (b (D (axis j)) (D (axis i))) = b (D (axis i)) (D (axis j))
    rw [star_trivial]
    exact g.symm _ _ _
  · intro v hv
    let v' : X n := WithLp.toLp 2 v
    have hv' : v' ≠ 0 := fun h => hv (congrArg WithLp.ofLp h)
    have hsum : D v' = ∑ i : I n, v i • D (axis i) := by
      conv_lhs => rw [← vector_eq_sum_axis v', map_sum]
      simp only [map_smul]
      rfl
    have hPair : metricPair (chartMetric g p) x v' v' = b (D v') (D v') := by
      change (∑ i, ∑ j, b (D (axis i)) (D (axis j)) * v i * v j) = b (D v') (D v')
      rw [hsum]
      simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        change b (D (axis i)) (D (axis j)) * v i * v j = v j * (v i * b (D (axis i)) (D (axis j)))
        ring
    rw [metricPair_eq_dotProduct] at hPair
    rw [show star v = v from star_trivial v]
    change 0 < (fun i => v' i) ⬝ᵥ (chartMetric g p x *ᵥ (fun i => v' i))
    rw [hPair]
    exact g.pos _ _ (fun h => hv' (hD.injective (h.trans (D.map_zero).symm)))

theorem chartMetric_smooth (g : SmoothMetric n M) (p : M) :
    CalderonN.SmoothMetric (extChartAt J p).target (chartMetric g p) :=
  ⟨chartMetric_smooth_entries g p, fun _ hx => chartMetric_posDef g p hx⟩

variable [MeasurableSpace M] [BorelSpace M]

/-- The canonical density gives a locally finite volume measure at
boundary points as well as at interior points. -/
theorem metricVolume_isLocallyFiniteMeasure (g : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun p => ?_⟩
  let e := extChartAt J p
  let d : X n → ℝ := fun x => Real.sqrt (chartMetric g p x).det
  have hc : ContinuousOn d e.target :=
    (CalderonN.contDiffOn_metric_volume (chartMetric_smooth g p)).continuousOn
  have hep : e p ∈ e.target := mem_extChartAt_target p
  have hNear : ∀ᶠ x in 𝓝[e.target] e p, d x < d (e p) + 1 :=
    (hc (e p) hep).eventually_lt continuousWithinAt_const (lt_add_one _)
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhdsWithin_iff.mp hNear
  let O := e.source ∩ e ⁻¹' ball (e p) r
  have hOpen : IsOpen O := (continuousOn_extChartAt (I := J) p).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := J) p) isOpen_ball
  have hpO : p ∈ O := ⟨mem_extChartAt_source p, mem_ball_self hr⟩
  refine ⟨O, hOpen.mem_nhds hpO, ?_⟩
  have hs := (isOpen_extChartAt_source (I := J) p).measurableSet
  have hB : MeasurableSet (ball (e p) r) := isOpen_ball.measurableSet
  have hMc : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    (continuousOn_extChartAt (I := J) p).aemeasurable hs
  have hMap := Measure.map_apply_of_aemeasurable hMc hB
  rw [hμ p, Measure.restrict_apply' hs, inter_comm, ← show O = e.source ∩ e ⁻¹' ball (e p) r from rfl,
    withDensity_apply _ hB] at hMap
  rw [← hMap]
  let ν := ((volume : Measure (X n)).restrict e.target).restrict (ball (e p) r)
  have hBound : ∀ᵐ x ∂ν, ENNReal.ofReal (d x) ≤ ENNReal.ofReal (d (e p) + 1) := by
    have ht : MeasurableSet e.target := by
      change MeasurableSet (extChartAt J p).target
      rw [extChartAt_target]
      exact (((chartAt (EuclideanHalfSpace n) p).open_target).preimage (J).continuous_symm).measurableSet.inter
        (J).isClosed_range.measurableSet
    have hv : ν = (volume : Measure (X n)).restrict (ball (e p) r ∩ e.target) := Measure.restrict_restrict hB
    rw [hv]
    filter_upwards [ae_restrict_mem (hB.inter ht)] with x hx
    exact ENNReal.ofReal_le_ofReal (hrB hx).le
  change (∫⁻ x, ENNReal.ofReal (d x) ∂ν) < ⊤
  refine (lintegral_mono_ae hBound).trans_lt ?_
  rw [lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((Measure.restrict_le_self (s := e.target) (μ := (volume : Measure (X n))) (ball (e p) r)).trans_lt
      measure_ball_lt_top)

theorem metricVolume_isFiniteMeasure [CompactSpace M] (g : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) : IsFiniteMeasure μ := by
  let _ := metricVolume_isLocallyFiniteMeasure g μ hμ
  exact ⟨isCompact_univ.measure_lt_top⟩

end CalderonPatch
