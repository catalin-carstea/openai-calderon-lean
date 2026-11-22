module

public import Proof.CalderonPatch.NormalChartSobolev
public import Proof.CalderonPatch.NormalChartZeroTrace
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Regularity.SmoothFlatBoundary

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

/-- The canonical weak inverse has a second-order Sobolev
representative on a smaller compactly contained normal half-chart.
The forcing hypothesis is local and includes forcing that vanishes on the chart. -/
theorem NativeBoundaryMetricChart.exists_sobolev_two_reading
    (D : DirichletData m M) {p : M} (A : NativeBoundaryMetricChart D.metric p)
    {W C : Set (X N)} (hW : IsOpen W) (hC : IsCompact C) (hCn : C.Nonempty)
    (hCA : C ⊆ A.ambient) (hWC : W ⊆ C) (hAE : W ∩ positiveHalfSpace N =ᵐ[μ] C)
    {V : Opens (X N)} (hVc : IsCompact (closure (V : Set (X N)))) (hVW : closure (V : Set (X N)) ⊆ W)
    (f : Lp ℝ 2 D.volume) {q : M → ℝ} (hq : ContinuousOn q A.coord.source)
    (hf : (f : M → ℝ) =ᵐ[D.volume.restrict A.coord.source] q) :
    ∃ U : Wkp μ (⟨(V : Set (X N)) ∩ positiveHalfSpace N,
          V.isOpen.inter isOpen_positiveHalfSpace⟩ : Opens (X N)) 2 2,
      (Wkp.value 2 U : X N → ℝ) =ᵐ[(μ).restrict ((V : Set (X N)) ∩ positiveHalfSpace N)]
        (D.l2Value (D.weakDirichletInverse f) : M → ℝ) ∘ A.coord.symm := by
  obtain ⟨e,heT,heInv,F,hValue,hValueTests,hRepr,hEq⟩ := A.exists_sobolev_reading_of_local D hW hC hCn hCA hWC hAE
  let H : Opens (X N) := ⟨positiveHalfSpace N,isOpen_positiveHalfSpace⟩
  let Ω : Opens (X N) := ⟨e.target,e.open_target⟩
  let U₀ : Opens (X N) := V ⊓ H
  have hΩH : Ω ≤ H := by
    intro x hx
    change x ∈ e.target at hx
    rw [heT] at hx
    exact hx.2
  have hUΩ : U₀ ≤ Ω := by
    intro x hx
    change x ∈ e.target
    rw [heT]
    exact ⟨hVW (subset_closure hx.1),hx.2⟩
  have heC : e.target ⊆ C := fun x hx => hWC (heT ▸ hx).1
  have heCI : e.target ⊆ C ∩ inwardHalfSpace N :=
    fun x hx => ⟨heC hx,positiveHalfSpace_subset_inwardHalfSpace (hΩH hx)⟩
  have hCI : C ∩ inwardHalfSpace N ⊆ A.coord.target := fun x hx =>
    A.target_eq.symm ▸ ⟨hCA hx.1,hx.2⟩
  have heS : e.source ⊆ A.coord.source := by
    intro x hx
    rw [← e.left_inv hx, heInv]
    exact A.coord.map_target (hCI (heCI (e.map_source hx)))
  let Q : X N → ℝ := fun z => q (A.coord.symm z) * chartVolume A.field z
  have hQc : ContinuousOn Q (C ∩ inwardHalfSpace N) :=
    (hq.comp (A.smooth_inverse.continuousOn.mono hCI)
      (fun z hz => A.coord.map_target (hCI hz))).mul
        ((CalderonN.continuousOn_metricVolumeDensity A.smooth_field).mono
          (fun z hz => hCA hz.1))
  have hC₀ : IsClosed (inwardHalfSpace N) :=
    isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : I N)).continuous
  have hCc : IsCompact (C ∩ inwardHalfSpace N) := hC.inter_right hC₀
  obtain ⟨B,hB⟩ := hCc.exists_bound_of_continuousOn hQc
  have hΩb : Bornology.IsBounded (Ω : Set (X N)) := hC.isBounded.subset heC
  let : IsFiniteMeasure ((μ).restrict e.target) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono heC).trans_lt hC.measure_lt_top⟩
  have hQ : MemLp Q 2 ((μ).restrict e.target) := by
    apply MemLp.of_bound
      ((hQc.mono heCI).aestronglyMeasurable e.open_target.measurableSet) B
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    exact hB z (heCI hz)
  let fΩ : Lp ℝ 2 ((μ).restrict e.target) := hQ.toLp Q
  obtain ⟨a,U,lam,Lam,L,hU,hCU,hUA,hAeq,ha,haS,haE,haL,haPos⟩ :=
    exists_smooth_divergenceMatrix_extension A.open_ambient A.smooth_field hC hCA
  have hAcoord : Set.EqOn a (fun z => Matrix.of (divergenceCoeff A.field z)) e.target :=
    hAeq.mono (heC.trans hCU)
  let u := F (D.weakDirichletInverse f)
  have hu (φ : 𝓓(Ω, ℝ)) : energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ μ Ω 2 φ) =
      ∫ x in Ω, fΩ x * φ x ∂μ := by
    have hEq' := hEq f (hq.mono heS) (ae_restrict_of_ae_restrict_of_subset heS hf) φ
    rw [energyFormH1_def] at hEq' ⊢
    refine (integral_congr_ae ?_).trans (hEq'.trans (integral_congr_ae ?_))
    · filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
      rw [hAcoord hz]
    · filter_upwards [hQ.coeFn_toLp] with z hz
      change (q (e.symm z) * chartVolume A.field z) * φ z = fΩ z * φ z
      rw [heInv]
      exact congrArg (fun a => a * φ z) hz.symm
  obtain ⟨ψ,B',hψ,_,hψ1,_,hψs,hB',hψB,hψg⟩ :=
    hVc.exists_contDiff_cutoff_with_bounds hW hVW
  have hRepr' (w : DirichletTest D) : ∃ v : X N → ℝ,
      Continuous v ∧ (∀ z ∈ closure (Ω : Set (X N)), z 0 = 0 → v z = 0) ∧
        (W1p.value (F (w : DirichletHilbert D)) : X N → ℝ) =ᵐ[(μ).restrict Ω] v := by
    obtain ⟨v,hv,_,hvEq,hv0⟩ := hRepr w
    refine ⟨v,hv.continuous,fun z hz => hv0 z ((closure_minimal heC hC.isClosed) hz),?_⟩
    refine (hValueTests w).trans ?_
    exact (ae_restrict_mem e.open_target.measurableSet).mono fun z hz => hvEq (heCI hz)
  have hZero := chartSobolev_cutoff_mem_w1p0 D heT hΩb F hRepr'
    hψ hψs hB' (fun z _ => hψB z) (fun z _ => hψg z) (D.weakDirichletInverse f)
  have hts : tsupport ψ ∩ H ⊆ (Ω : Set (X N)) := by
    intro z hz
    change z ∈ e.target
    rw [heT]
    exact ⟨hψs hz.1,hz.2⟩
  let ν : X N := EuclideanSpace.basisFun (I N) ℝ 0
  have hν : ν ≠ 0 := by
    intro he
    have h := congrArg (fun z : X N => z 0) he
    simpa [ν,EuclideanSpace.basisFun_apply] using h
  have hH (z : X N) : z ∈ H ↔ 0 < ⟪z, ν⟫ := by
    change 0 < z 0 ↔ 0 < ⟪z, ν⟫
    simp [ν,EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_right]
  have hψEq (z : X N) (hz : z ∈ U₀) : ψ z = 1 :=
    mem_singleton_iff.1
      (show z ∈ ψ ⁻¹' ({1} : Set ℝ) from interior_subset (hψ1 (subset_closure hz.1)))
  obtain ⟨Z,hZ⟩ := exists_wkp_two_of_smoothCutoff hν hH haE haL ha haS haPos hΩH hUΩ hΩb
    hu hψ hts hB' (fun z _ => hψB z) (fun z _ => hψg z) hZero hψEq
  refine ⟨Z,hZ.trans ?_⟩
  rw [← heInv]
  exact ae_restrict_of_ae_restrict_of_subset hUΩ (hValue (D.weakDirichletInverse f))

end CalderonPatch
