module

public import Proof.CalderonPatch.NormalChartSobolev
public import Proof.CalderonPatch.NormalChartZeroTrace
public import Proof.CalderonPatch.HalfSpaceHigherOrder
public import Proof.CalderonPatch.LocalizedSobolevReadings

import Proof.CalderonPatch.HalfSpaceTangentialTrace
import Proof.CalderonN.CompactSmoothExtension

import Proof.CalderonPatch.ChartEllipticExtension
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace TauCeti TauCeti.PDE
open scoped ContDiff Distributions ENNReal Gradient Manifold Matrix.Norms.Elementwise RealInnerProductSpace

namespace CalderonPatch

open CalderonN (X I chartVolume divergenceCoeff)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "μ" => (volume : Measure (X N))

omit [PreconnectedSpace M] in
private theorem exists_smooth_chart_forcing
    {g : SmoothMetric N M} {p : M} (A : NativeBoundaryMetricChart g p)
    {C : Set (X N)} (hC : IsCompact C) (hCA : C ⊆ A.ambient)
    {q : M → ℝ} (hq : ContMDiff J 𝓘(ℝ,ℝ) ∞ q) :
    ∃ Q : X N → ℝ, ContDiff ℝ ∞ Q ∧ EqOn Q
      (fun z => q (A.coord.symm z) * chartVolume A.field z) (C ∩ inwardHalfSpace N) := by
  obtain ⟨v,V,hv,hV,hCV,hVA,hvEq⟩ := A.exists_smooth_function_extension hq hC hCA
  obtain ⟨ρ,hρ,_,W,_,hCW,_,hρEq⟩ := CalderonN.exists_contDiff_extension_near_compact
    A.open_ambient hC hCA (CalderonN.contDiffOn_metric_volume A.smooth_field)
  refine ⟨fun z => v z * ρ z,hv.mul hρ,?_⟩
  intro z hz
  change v z * ρ z = q (A.coord.symm z) * chartVolume A.field z
  rw [show v z = q (A.coord.symm z) from hvEq ⟨hCV hz.1,hz.2⟩,hρEq (hCW hz.1)]
  rfl

set_option maxHeartbeats 3000000 in
/-- Localized Sobolev readings of every finite order on the
coordinate half-space, with first-order zero trace. -/
theorem NativeBoundaryMetricChart.exists_localized_sobolev_order
    (D : DirichletData m M) {p : M} (A : NativeBoundaryMetricChart D.metric p)
    {W C : Set (X N)} (hW : IsOpen W) (hC : IsCompact C) (hCn : C.Nonempty)
    (hCA : C ⊆ A.ambient) (hWA : W ⊆ A.ambient) (hWC : W ∩ positiveHalfSpace N ⊆ C) (hAE : W ∩ positiveHalfSpace N =ᵐ[μ] C)
    (f : Lp ℝ 2 D.volume) {q : M → ℝ} (hq : ContMDiff J 𝓘(ℝ,ℝ) ∞ q)
    {U₀ : Set M} (hSrc : A.coord.symm '' (C ∩ inwardHalfSpace N) ⊆ U₀)
    (hf : (f : M → ℝ) =ᵐ[D.volume.restrict U₀] q)
    {ψ : X N → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ W) (k : ℕ) :
    ∃ U : Wkp μ (positiveHalfSpaceOpens N) 2 (k+1),
      Wkp.firstOrder k U ∈ w1p0Submodule μ (positiveHalfSpaceOpens N) 2 ∧
      (Wkp.value (k+1) U : X N → ℝ) =ᵐ[(μ).restrict (W ∩ positiveHalfSpace N)]
        fun z => ψ z * D.l2Value (D.weakDirichletInverse f) (A.coord.symm z) := by
  obtain ⟨e,heT,heInv,F,hValue,hValueTests,hRepr,hEq⟩ := A.exists_sobolev_reading_in_signed_region D hW hC hCn hCA hWA hWC hAE
  let H : Opens (X N) := positiveHalfSpaceOpens N
  let Ω : Opens (X N) := ⟨e.target,e.open_target⟩
  have hΩH : Ω ≤ H := by
    intro x hx
    change x ∈ e.target at hx
    rw [heT] at hx
    exact hx.2
  have heC : e.target ⊆ C := fun x hx => hWC (heT ▸ hx)
  have heCI : e.target ⊆ C ∩ inwardHalfSpace N :=
    fun x hx => ⟨heC hx,positiveHalfSpace_subset_inwardHalfSpace (hΩH hx)⟩
  have hCI : C ∩ inwardHalfSpace N ⊆ A.coord.target := fun x hx =>
    A.target_eq.symm ▸ ⟨hCA hx.1,hx.2⟩
  have heS : e.source ⊆ U₀ := by
    intro x hx
    rw [← e.left_inv hx, heInv]
    exact hSrc (mem_image_of_mem A.coord.symm (heCI (e.map_source hx)))
  obtain ⟨Q,hQ,hQeq⟩ := exists_smooth_chart_forcing A hC hCA hq
  have hΩb : Bornology.IsBounded (Ω : Set (X N)) := hC.isBounded.subset heC
  let : IsFiniteMeasure ((μ).restrict e.target) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono heC).trans_lt hC.measure_lt_top⟩
  obtain ⟨B,hB⟩ := hC.exists_bound_of_continuousOn hQ.continuous.continuousOn
  have hQLp : MemLp Q 2 ((μ).restrict e.target) := by
    apply MemLp.of_bound hQ.continuous.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    exact hB z (heC hz)
  let fΩ : Lp ℝ 2 ((μ).restrict e.target) := hQLp.toLp Q
  obtain ⟨a,U,lam,Lam,L,hU,hCU,hUA,hAeq,ha,haS,haE,haL,haPos,haCompact⟩ :=
    exists_smooth_divergenceMatrix_extension_constantOutside A.open_ambient A.smooth_field hC hCA
  have hAcoord : EqOn a (fun z => Matrix.of (divergenceCoeff A.field z)) e.target :=
    hAeq.mono (heC.trans hCU)
  let u := F (D.weakDirichletInverse f)
  have hu (φ : 𝓓(Ω, ℝ)) : energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ μ Ω 2 φ) =
      ∫ x in Ω, fΩ x * φ x ∂μ := by
    have hEq' := hEq f hq.continuous.continuousOn (ae_restrict_of_ae_restrict_of_subset heS hf) φ
    rw [energyFormH1_def] at hEq' ⊢
    refine (integral_congr_ae ?_).trans (hEq'.trans (integral_congr_ae ?_))
    · filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
      rw [hAcoord hz]
    · filter_upwards [hQLp.coeFn_toLp,ae_restrict_mem e.open_target.measurableSet] with z hz hzT
      change (q (e.symm z) * chartVolume A.field z) * φ z = fΩ z * φ z
      rw [heInv, hz, hQeq (heCI hzT)]
  have hRepr' (w : DirichletTest D) : ∃ v : X N → ℝ,
      Continuous v ∧ (∀ z ∈ closure (Ω : Set (X N)), z 0 = 0 → v z = 0) ∧
        (W1p.value (F (w : DirichletHilbert D)) : X N → ℝ) =ᵐ[(μ).restrict Ω] v := by
    obtain ⟨v,hv,_,hvEq,hv0⟩ := hRepr w
    refine ⟨v,hv.continuous,fun z hz => hv0 z ((closure_minimal heC hC.isClosed) hz),?_⟩
    refine (hValueTests w).trans ?_
    exact (ae_restrict_mem e.open_target.measurableSet).mono fun z hz => hvEq (heCI hz)
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ ((μ).restrict H) := by
    exact memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) haE.upper_nonneg
      ha.continuous.aestronglyMeasurable aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x _ => haE.upper_bound (mem_univ x)) (by simp) (by simp)
  obtain ⟨Z,hZero,hZ,_⟩ := CalderonPatch.exists_localized_sobolev_order hW hΩH hΩb
    (by intro x hx; change x ∈ e.target; rw [heT]; exact hx) ha hcoeff
    (exists_halfSpace_higher_solution_of_tangential_trace ha haCompact haE haL haS haPos
      wkp_two_tangential_derivative_mem_w1p0)
    hQ hQLp.coeFn_toLp u hu
    (fun ζ hζ _ hζs B hB hv hg =>
      chartSobolev_cutoff_mem_w1p0 D heT hΩb F hRepr' hζ hζs hB hv hg
        (D.weakDirichletInverse f)) k hψ hψc hψs
  refine ⟨Z,hZero,?_⟩
  rw [← heInv,← heT,← Wkp.value_firstOrder]
  filter_upwards [hZ.filter_mono (ae_mono (Measure.restrict_mono_set _ hΩH)),
    hValue (D.weakDirichletInverse f),ae_restrict_mem e.open_target.measurableSet] with z hz hv hzT
  rw [hz,indicator_of_mem (show z ∈ (Ω : Set (X N)) from hzT),hv,Function.comp_apply]

end CalderonPatch
