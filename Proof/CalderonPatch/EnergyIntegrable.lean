module

public import Proof.CalderonPatch.LocalStationarity

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricCalculus

public section

noncomputable section
open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (I X InteriorMetricChart MetricField chartMetricGradient chartVolume chartVolumeMeasure coordDeriv)

variable {n : ℕ} [NeZero n] {M : Type*}
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

omit [IsManifold (𝓡∂ n) ∞ M] in
private theorem integrableOn_of_coordinateRepresentation
    {μ : Measure M} {L : (M → ℝ) → M → ℝ} (C : InteriorMetricChart J μ L)
    {f : X n → ℝ} {w : M → ℝ}
    (hInt : IntegrableOn (fun x => chartVolume C.metric x * f x) C.chart.target)
    (hW : EqOn (w ∘ C.chart.symm) f C.chart.target) :
    IntegrableOn w C.chart.source μ := by
  let e := C.chart
  have hDensity := (CalderonN.continuousOn_metricVolumeDensity C.smooth_metric).aemeasurable
    e.open_target.measurableSet (μ := (volume : Measure (X n)))
  have hF : Integrable f (chartVolumeMeasure e.target C.metric) := by
    unfold chartVolumeMeasure
    apply (integrable_withDensity_iff_integrable_smul₀' hDensity.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    simp only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _),smul_eq_mul]
    exact hInt
  have he : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hMap : Integrable f ((μ.restrict e.source).map e) := C.volume_eq.symm ▸ hF
  have hPull : IntegrableOn (f ∘ e) e.source μ :=
    (integrable_map_measure hMap.aestronglyMeasurable he).mp hMap
  refine hPull.congr_fun ?_ e.open_source.measurableSet
  intro x hx
  have h := hW (e.map_source hx)
  rw [Function.comp_apply,e.left_inv hx] at h
  exact h.symm

private theorem integrableOn_pairing_in_compact_coordinate_region (g : SmoothMetric n M)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X n)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {u v : M → ℝ} (hu : ContMDiffOn J R ∞ u e.source) (hv : ContMDiffOn J R ∞ v e.source)
    {C U : Set (X n)} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U) (heC : e.target ⊆ C)
    {γ : MetricField n} (hγ : CalderonN.SmoothMetric U γ)
    (hMetric : EqOn (coordinateMetric g e) γ e.target)
    {a b : X n → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hA : EqOn (u ∘ e.symm) a e.target) (hB : EqOn (v ∘ e.symm) b e.target) :
    IntegrableOn (energyPairingDensity g u v) e.source μ := by
  let D := nativeInteriorMetricChart g μ hμ e heI he hes
  let f (x : X n) := ∑ i : I n, coordDeriv i b x * chartMetricGradient γ a x i
  have hf : ContinuousOn f U := by
    apply ContDiffOn.continuousOn (𝕜 := ℝ) (n := ∞)
    apply ContDiffOn.sum
    intro i _
    apply (CalderonN.contDiffOn_coordDeriv hb hU i).mul
    change ContDiffOn ℝ ∞ (fun x => ∑ j : I n, (γ x)⁻¹ i j * coordDeriv j a x) U
    exact ContDiffOn.sum fun j _ => (CalderonN.contDiffOn_metric_inv_entry hγ i j).mul
      (CalderonN.contDiffOn_coordDeriv ha hU j)
  have hfρ : ContinuousOn (fun x => chartVolume γ x * f x) U :=
    (CalderonN.continuousOn_metricVolumeDensity hγ).mul hf
  have hIC : IntegrableOn (fun x => chartVolume γ x * f x) C :=
    (hfρ.mono hCU).integrableOn_compact hC
  apply integrableOn_of_coordinateRepresentation D (f := f)
  · apply (hIC.mono_set heC).congr_fun _ e.open_target.measurableSet
    intro x hx
    change chartVolume γ x * f x = chartVolume (coordinateMetric g e) x * f x
    exact congrArg (fun G : CalderonN.Mat n => Real.sqrt G.det * f x) (hMetric hx).symm
  · intro x hx
    have h := energyPairingDensity_in_coordinates g e he hes hu hv hx
    change energyPairingDensity g u v (e.symm x) = f x
    rw [h]
    have hDa (i : I n) := CalderonN.eqOn_coordDeriv e.open_target hA i hx
    have hDb (i : I n) := CalderonN.eqOn_coordDeriv e.open_target hB i hx
    simp only [f,chartMetricGradient,hMetric hx,hDa,hDb]

variable [T2Space M] [CompactSpace M]

local notation "H" => inwardHalfSpace n

private theorem exists_neighborhood_integrable_pairing_at_interior (g : SmoothMetric n M)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    {u v : M → ℝ} (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    {p : M} (hp : p ∈ (J).interior M) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ IntegrableOn (energyPairingDensity g u v) V μ := by
  obtain ⟨e,hPe,_,heI,he,hes⟩ := exists_interiorChart p hp isOpen_univ (mem_univ p)
  let q := e p
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hPe))
  let B := ball q (r / 2)
  let C := closedBall q (r / 2)
  have hC : C ⊆ e.target := (closedBall_subset_ball (by linarith)).trans hBall
  have hB : B ⊆ e.target := ball_subset_closedBall.trans hC
  let A := nativeInteriorMetricChart g μ hμ e heI he hes
  obtain ⟨D,hS,hT,hInv,_⟩ := restrict_interiorMetricChart A isOpen_ball hB
  refine ⟨D.chart.source,D.chart.open_source,?_,?_⟩
  · rw [hS]
    exact ⟨hPe,mem_ball_self (by positivity)⟩
  have hInv' : (D.chart.symm : X n → M) = e.symm := hInv
  have hγ : EqOn (coordinateMetric g D.chart) (coordinateMetric g e) D.chart.target := by
    intro x _
    change (fun i j => g.inner (D.chart.symm x)
      (mfderiv K J D.chart.symm x (CalderonN.axis i))
      (mfderiv K J D.chart.symm x (CalderonN.axis j))) = coordinateMetric g e x
    rw [hInv']
    rfl
  apply integrableOn_pairing_in_compact_coordinate_region g μ hμ D.chart D.source_interior
    D.smooth D.smooth_inverse hu.contMDiffOn hv.contMDiffOn e.open_target (isCompact_closedBall q (r / 2)) hC
    (hT.symm ▸ ball_subset_closedBall) A.smooth_metric hγ
    (hu.comp_contMDiffOn hes).contDiffOn (hv.comp_contMDiffOn hes).contDiffOn
  · rw [hInv']; exact fun _ _ => rfl
  · rw [hInv']; exact fun _ _ => rfl

/-- The polarized energy of smooth functions is integrable against
the metric volume on a compact manifold with boundary. -/
theorem integrable_energyPairingDensity
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
    (g : SmoothMetric (m + 1) M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    {u v : M → ℝ} (hu : ContMDiff (𝓡∂ (m + 1)) R ∞ u) (hv : ContMDiff (𝓡∂ (m + 1)) R ∞ v) :
    Integrable (energyPairingDensity g u v) μ := by
  let I₀ := (𝓡∂ (m + 1)).interior M
  have hAE : ∀ᵐ x ∂μ, x ∈ I₀ := by
    rw [ae_iff]
    change μ (I₀ᶜ) = 0
    rw [show I₀ᶜ = (𝓡∂ (m + 1)).boundary M from (𝓡∂ (m + 1)).compl_interior]
    exact metricVolume_boundary_eq_zero g μ hμ
  have hLocal (p : M) :
      ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ IntegrableOn (energyPairingDensity g u v) V μ := by
    by_cases hp : p ∈ I₀
    · exact exists_neighborhood_integrable_pairing_at_interior g μ hμ hu hv hp
    have hpB : p ∈ (𝓡∂ (m + 1)).boundary M := by
      rw [← (𝓡∂ (m + 1)).compl_interior (M := M)]
      exact hp
    obtain ⟨D⟩ := exists_nativeBoundaryMetricChart g p hpB
    obtain ⟨a,b,_,hBottom,_,hpBox,hBox⟩ := D.exists_normalHalfBox
    let C := (WithLp.toLp 2) '' Icc a b
    have hC : IsCompact C := isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : I (m + 1) => ℝ))
    have hCD : C ⊆ D.ambient := image_subset_iff.mpr hBox
    obtain ⟨u₀,U₁,hu₀,hU₁,hCU₁,hU₁D,hU⟩ := D.exists_smooth_function_extension hu hC hCD
    obtain ⟨v₀,U₂,hv₀,hU₂,hCU₂,hU₂D,hV⟩ := D.exists_smooth_function_extension hv hC hCD
    let U := U₁ ∩ U₂
    have hUD : U ⊆ D.ambient := inter_subset_left.trans hU₁D
    let W : Set (X (m + 1)) := WithLp.ofLp ⁻¹' (univ.pi fun i : I (m + 1) => Ioo (a i) (b i))
    have hW : IsOpen W := (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).preimage
      (PiLp.continuous_ofLp 2 (fun _ : I (m + 1) => ℝ))
    have hWC : W ⊆ C := by
      intro x hx
      have hh := Set.mem_pi.mp hx
      refine ⟨WithLp.ofLp x,⟨fun i => (hh i (mem_univ i)).1.le,fun i => (hh i (mem_univ i)).2.le⟩,?_⟩
      exact WithLp.toLp_ofLp 2 x
    have hCU : C ⊆ U := subset_inter hCU₁ hCU₂
    obtain ⟨e,hET,_,hInv,heI,he,hes,hMetric⟩ := D.exists_interior_restriction hW (hWC.trans hCD)
    have heC : e.target ⊆ C := hET.symm ▸ (inter_subset_left.trans hWC)
    have heU : e.target ⊆ U ∩ inwardHalfSpace (m + 1) := by
      refine subset_inter (heC.trans hCU) ?_
      rw [hET]
      exact inter_subset_right.trans positiveHalfSpace_subset_inwardHalfSpace
    have hReprU : EqOn (u ∘ e.symm) u₀ e.target := by
      rw [hInv]
      exact hU.symm.mono (heU.trans (inter_subset_inter_left _ inter_subset_left))
    have hReprV : EqOn (v ∘ e.symm) v₀ e.target := by
      rw [hInv]
      exact hV.symm.mono (heU.trans (inter_subset_inter_left _ inter_subset_right))
    have hγ : CalderonN.SmoothMetric U D.field :=
      ⟨fun i j => (D.smooth_field.1 i j).mono hUD,fun x hx => D.smooth_field.2 x (hUD hx)⟩
    have hE := integrableOn_pairing_in_compact_coordinate_region g μ hμ e heI he hes
      hu.contMDiffOn hv.contMDiffOn (hU₁.inter hU₂) hC hCU heC hγ hMetric
      hu₀.contDiffOn hv₀.contDiffOn hReprU hReprV
    let A := D.coord.source ∩ D.coord ⁻¹' normalHalfBox a b
    have hSub : A ∩ I₀ ⊆ e.source := by
      intro x hx
      have hxD : x ∈ D.coord.source := hx.1.1
      have hxBox : D.coord x ∈ normalHalfBox a b := hx.1.2
      have hxP := (D.interior_iff x hxD).mp hx.2
      have hxW : D.coord x ∈ W := by
        apply Set.mem_pi.mpr
        intro i _
        change a i < D.coord x i ∧ D.coord x i < b i
        refine ⟨?_,hxBox.2.1 i⟩
        by_cases hi : i = 0
        · subst i
          exact hBottom.symm ▸ mem_positiveHalfSpace.mp hxP
        · exact hxBox.2.2 i hi
      have ht : D.coord x ∈ e.target := hET.symm ▸ ⟨hxW,hxP⟩
      have hs := e.map_target ht
      rwa [hInv,D.coord.left_inv hxD] at hs
    refine ⟨A,D.isOpen_preimage_normalHalfBox a b,⟨D.point_source,hpBox⟩,?_⟩
    apply (hE.mono_set hSub).congr_set_ae
    filter_upwards [hAE] with x hx
    simp [hx]
  choose V hVo hVp hVI using hLocal
  have hCover : (univ : Set M) ⊆ ⋃ p, V p := fun p _ => mem_iUnion.mpr ⟨p,hVp p⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover V hVo hCover
  have hInt : IntegrableOn (energyPairingDensity g u v) (⋃ p ∈ s, V p) μ :=
    integrableOn_finset_iUnion.mpr (fun p _ => hVI p)
  exact integrableOn_univ.mp (hInt.mono_set hs)

end CalderonPatch
