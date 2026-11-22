module

public import Proof.CalderonPatch.ChartWeakEquation
public import Proof.CalderonPatch.LocalizedSobolevReadings

import Proof.CalderonPatch.ChartCompactRegions
import Proof.CalderonPatch.ChartEllipticExtension
import Proof.CalderonPatch.InteriorChartBasis
import Proof.CalderonPatch.InverseChartAE
import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.SobolevInteriorRepresentative
import Proof.CalderonN.WeakTest
import Proof.CalderonN.WholeSpaceRegularity
import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.CompactSupport
import Mathlib.Tactic

public section

noncomputable section

open Filter MeasureTheory Set Metric TopologicalSpace TauCeti TauCeti.PDE
open scoped ContDiff Distributions ENNReal Gradient Manifold Matrix.Norms.Elementwise

namespace CalderonPatch

open CalderonN (X I Mat chartVolume divergenceCoeff)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (m+1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "K" => 𝓘(ℝ, X N)
local notation "μ" => (volume : Measure (X N))

private theorem lipschitzWith_matrix_entries {n : ℕ} {a : X n → Mat n} {B : NNReal}
    (h : LipschitzWith B fun z => matrixBilinearForm (a z)) (i j : I n) :
    LipschitzWith B fun z => a z i j := by
  let v := CalderonN.WeakTest.e i
  let w := CalderonN.WeakTest.e j
  have hv : ‖v‖ = 1 := by simp [v,CalderonN.WeakTest.e]
  have hw : ‖w‖ = 1 := by simp [w,CalderonN.WeakTest.e]
  have hEntry (z : X n) : matrixBilinearForm (a z) v w = a z i j := by
    simp [v,w,CalderonN.WeakTest.e]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,← hEntry x,← hEntry y,← Real.norm_eq_abs]
  let A := matrixBilinearForm (a x) - matrixBilinearForm (a y)
  have hA : ‖A v w‖ ≤ ‖A‖ := by
    simpa only [hv,hw,mul_one] using A.le_opNorm₂ v w
  change ‖A v w‖ ≤ _
  exact hA.trans (by simpa only [dist_eq_norm] using h.dist_le_mul x y)

set_option maxHeartbeats 4000000 in
/-- The native weak inverse has a smooth representative on a
neighborhood of each interior point with local smooth forcing. -/
theorem exists_weakInverse_interior_smooth_rep (D : DirichletData m M)
    {U : Set M} (hU : IsOpen U) {p : M} (hp : p ∈ U) (hpI : p ∈ (J).interior M)
    (f : Lp ℝ 2 D.volume) {q : M → ℝ} (hq : ContMDiff J R ∞ q)
    (hf : (f : M → ℝ) =ᵐ[D.volume.restrict U] q) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ (J).interior M ∧
      ∃ u : M → ℝ, ContMDiffOn J R ∞ u V ∧
        (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict V] u := by
  obtain ⟨e,hPe,heU,heI,he,hes⟩ := exists_interiorChart p hpI hU hp
  let c := e p
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hPe))
  let W := ball c (r / 2)
  let C := closedBall c (r / 2)
  have hr₂ : 0 < r/2 := half_pos hr
  have hC : IsCompact C := isCompact_closedBall _ _
  have hCW : W ⊆ C := ball_subset_closedBall
  have hCT : C ⊆ e.target := (closedBall_subset_ball (half_lt_self hr)).trans hR
  let T := nativeInteriorMetricChart D.metric D.volume D.metric_volume e heI he hes
  obtain ⟨A,hSource,hTarget,hInv,_⟩ := restrict_interiorMetricChart T isOpen_ball (hCW.trans hCT)
  let b := A.chart
  let Ω : Opens (X N) := ⟨b.target,b.open_target⟩
  have hbT : b.target = W := hTarget
  have hbS : b.source ⊆ e.source := fun _ hx => (hSource ▸ hx).1
  have hpB : p ∈ b.source := hSource.symm ▸ ⟨hPe,mem_ball_self hr₂⟩
  have hbC : b.target ⊆ C := hbT ▸ hCW
  have hbγ : EqOn (coordinateMetric D.metric b) (coordinateMetric D.metric e) b.target := by
    intro z _
    have hV : (b.symm : X N → M) = e.symm := hInv
    unfold coordinateMetric
    rw [hV]
  have hRepr (u : DirichletTest D) : ∃ v : X N → ℝ,
      ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ EqOn (u ∘ b.symm) v b.target := by
    have hh : ContDiffOn ℝ ∞ (u ∘ e.symm) e.target :=
      (u.smooth.comp_contMDiffOn hes).contDiffOn
    obtain ⟨v,hv,hvc,V,hV,hCV,_,hEq⟩ :=
      CalderonN.exists_contDiff_extension_near_compact e.open_target hC hCT hh
    exact ⟨v,hv,hvc,by rw [show (b.symm : X N → M) = e.symm from hInv]; exact hEq.symm.mono (hbC.trans hCV)⟩
  obtain ⟨F,hF⟩ := exists_dirichletHilbert_chartSobolev D b A.source_interior A.smooth A.smooth_inverse
    hC ⟨c,mem_closedBall_self hr₂.le⟩ hCT hbC
    (hbT.symm ▸ ae_ball_eq_closedBall c hr₂) T.smooth_metric hbγ hRepr
  obtain ⟨a,W',lam,Lam,L,hW',hCW',_,hAeq,ha,haS,hell,hLip,_,haComp⟩ :=
    exists_smooth_divergenceMatrix_extension_constantOutside e.open_target T.smooth_metric hC hCT
  have haB (z : X N) (hz : z ∈ b.target) : a z = chartDivergenceMatrix D.metric b z := by
    rw [hAeq (hCW' (hbC hz))]
    exact (congrArg (fun γ : Mat N => Matrix.of (fun i j => Real.sqrt γ.det * γ⁻¹ i j)) (hbγ hz)).symm
  let H : Opens (X N) := ⊤
  have hcoeff : MemLp (fun z => energyIntegrand (a z) 0 0) ⊤ ((μ).restrict H) := by
    exact memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hell.upper_nonneg
      ha.continuous.aestronglyMeasurable aestronglyMeasurable_const aestronglyMeasurable_const
      (fun z _ => hell.upper_bound (mem_univ z)) (by simp) (by simp)
  have hCoeff : MemLp (fun z => energyIntegrand (chartDivergenceMatrix D.metric b z) 0 0) ⊤
      ((μ).restrict b.target) := by
    have hsub : MemLp (fun z => energyIntegrand (a z) 0 0) ⊤ ((μ).restrict b.target) :=
      hcoeff.mono_measure (Measure.restrict_mono_set _ (subset_univ b.target))
    apply hsub.ae_eq
    filter_upwards [ae_restrict_mem b.open_target.measurableSet] with z hz
    rw [haB z hz]
  let Q₀ (z : X N) := q (e.symm z) * chartVolume (coordinateMetric D.metric e) z
  have hQ₀ : ContDiffOn ℝ ∞ Q₀ e.target :=
    ((hq.comp_contMDiffOn hes).contDiffOn).mul (CalderonN.contDiffOn_metric_volume T.smooth_metric)
  obtain ⟨Q,hQ,_,V,hV,hCV,_,hQeq⟩ := CalderonN.exists_contDiff_extension_near_compact e.open_target hC hCT hQ₀
  let : IsFiniteMeasure ((μ).restrict b.target) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hbC).trans_lt hC.measure_lt_top⟩
  obtain ⟨B,hB⟩ := hC.exists_bound_of_continuousOn hQ.continuous.continuousOn
  have hQLp : MemLp Q 2 ((μ).restrict b.target) := by
    apply MemLp.of_bound hQ.continuous.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem b.open_target.measurableSet] with z hz
    exact hB z (hbC hz)
  let fΩ : Lp ℝ 2 ((μ).restrict b.target) := hQLp.toLp Q
  let w := F (D.weakDirichletInverse f)
  have hWeak (φ : 𝓓(Ω, ℝ)) :
      energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ μ Ω 2 φ) = ∫ z in Ω, fΩ z * φ z := by
    have hEq := chartSobolev_weakDirichletInverse_test_of_local D b A.source_interior
      A.smooth A.smooth_inverse F hF (fun u => (hRepr u).imp fun _ h => ⟨h.1,h.2.2⟩)
      hCoeff f hq.continuous.continuousOn
      (ae_restrict_of_ae_restrict_of_subset (hbS.trans heU) hf) φ
    rw [energyFormH1_def] at hEq ⊢
    refine (integral_congr_ae ?_).trans (hEq.trans (integral_congr_ae ?_))
    · filter_upwards [ae_restrict_mem b.open_target.measurableSet] with z hz
      rw [haB z hz]
    · filter_upwards [hQLp.coeFn_toLp,ae_restrict_mem b.open_target.measurableSet] with z hz hzT
      change (q (b.symm z) * chartVolume (coordinateMetric D.metric b) z) * φ z = fΩ z * φ z
      rw [show (b.symm : X N → M) = e.symm from hInv,hz,hQeq (hCV (hbC hzT))]
      exact congrArg (fun γ => q (e.symm z) * Real.sqrt γ.det * φ z) (hbγ hzT)
  have hRead := dirichletHilbert_chartSobolev_value D b A.source_interior A.smooth A.smooth_inverse F hF
    (D.weakDirichletInverse f)
  have hLocal k {ψ : X N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
      (hψc : HasCompactSupport ψ) (hψT : tsupport ψ ⊆ b.target) :=
    exists_localized_sobolev_order b.open_target (le_top : Ω ≤ H) (hC.isBounded.subset hbC)
      inter_subset_left ha hcoeff
      (CalderonN.exists_wholeSpace_higher_solution ha haComp hell (lipschitzWith_matrix_entries hLip))
      hQ hQLp.coeFn_toLp w hWeak
      (fun ζ hζ hζc hζs B hB hv hg =>
        W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hζ hB hv hg hζc hζs w)
      k hψ hψc hψT
  have hSmooth : ∃ u : X N → ℝ, ContDiffOn ℝ ∞ u b.target ∧
      u =ᵐ[(μ).restrict b.target] (W1p.value w : X N → ℝ) := by
    apply CalderonN.exists_contDiffOn_ae_eq b.open_target
    intro x hx
    obtain ⟨s,hs,hS⟩ := Metric.mem_nhds_iff.mp (b.open_target.mem_nhds hx)
    let ρ := s/2
    have hρ : 0 < ρ := half_pos hs
    have hK : closedBall x ρ ⊆ b.target := (closedBall_subset_ball (half_lt_self hs)).trans hS
    refine ⟨ρ,hρ,ball_subset_closedBall.trans hK,fun k => ?_⟩
    obtain ⟨ψ,hψ,hψc,hψS,hψOne⟩ :=
      CalderonN.Elliptic.exists_plateau_cutoff b.open_target (isCompact_closedBall x ρ) hK
    obtain ⟨Z,_,hZ,_⟩ := hLocal k hψ hψc hψS
    let O : Opens (X N) := ⟨ball x ρ,isOpen_ball⟩
    let Z₀ := Wkp.lowerOrder k Z
    refine ⟨Wkp.restrictL (le_top : O ≤ H) k Z₀,
      (Wkp.value_restrictL_ae (le_top : O ≤ H) k Z₀).trans ?_⟩
    filter_upwards [hZ.filter_mono (ae_mono (Measure.restrict_mono_set _ (subset_univ (O : Set (X N))))),
      ae_restrict_mem O.isOpen.measurableSet] with z hz hzO
    change Wkp.value k (Wkp.lowerOrder k Z) z = _
    rw [← Wkp.value_succ,← Wkp.value_firstOrder,hz,indicator_of_mem (show z ∈ (Ω : Set (X N)) from hK (ball_subset_closedBall hzO)),
      (hψOne z (ball_subset_closedBall hzO)).eq_of_nhds,one_mul]
  obtain ⟨u,hu,hEq⟩ := hSmooth
  refine ⟨b.source,b.open_source,hpB,fun _ hx => ⟨heU (hbS hx),A.source_interior hx⟩,
    u ∘ b,hu.contMDiffOn.comp A.smooth (fun _ hx => b.map_source hx),?_⟩
  apply ae_native_of_ae_coordinate D.metric D.volume D.metric_volume b A.source_interior A.smooth A.smooth_inverse
  filter_upwards [hEq.trans hRead,ae_restrict_mem b.open_target.measurableSet] with z hz hzT
  simpa only [Function.comp_apply,b.right_inv hzT] using hz.symm

end CalderonPatch
