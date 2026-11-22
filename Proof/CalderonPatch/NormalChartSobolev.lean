module

public import Proof.CalderonPatch.ChartWeakEquation
public import Proof.CalderonPatch.NormalChartFunctions

import Proof.CalderonPatch.NormalChartInterior
import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.BumpFunction.Cutoff

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace TauCeti TauCeti.PDE
open scoped ContDiff Distributions ENNReal Manifold Matrix.Norms.Elementwise

namespace CalderonPatch

open CalderonN (X I Mat chartVolume divergenceCoeff contDiffOn_divergenceCoeff)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "K" => 𝓘(ℝ, X N)
local notation "R" => 𝓘(ℝ, ℝ)

omit [CompactSpace M] [T2Space M] [BorelSpace M] [PreconnectedSpace M] in
private theorem chartDivergenceMatrix_eq_signed (D : DirichletData m M)
    (e : OpenPartialHomeomorph M (X N)) {γ : CalderonN.MetricField N} {z : X N}
    (h : coordinateMetric D.metric e z = γ z) :
    chartDivergenceMatrix D.metric e z = Matrix.of (divergenceCoeff γ z) :=
  congrArg (fun a : Mat N => Matrix.of (fun i j => Real.sqrt a.det * a⁻¹ i j)) h

omit [PreconnectedSpace M] in
private theorem normalChart_coeff_memLp (D : DirichletData m M)
    {p : M} (A : NativeBoundaryMetricChart D.metric p)
    (e : OpenPartialHomeomorph M (X N))
    {C : Set (X N)} (hC : IsCompact C) (hCA : C ⊆ A.ambient) (hT : e.target ⊆ C)
    (hMetric : EqOn (coordinateMetric D.metric e) A.field e.target) :
    MemLp (fun z => energyIntegrand (chartDivergenceMatrix D.metric e z) 0 0) ⊤
      ((volume : Measure (X N)).restrict e.target) := by
  let a (z : X N) : Mat N := divergenceCoeff A.field z
  let : NormedAddCommGroup (X N →L[ℝ] X N →L[ℝ] ℝ) := inferInstance
  have ha : ContDiffOn ℝ ∞ a A.ambient :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => contDiffOn_divergenceCoeff A.smooth_field i j
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn (ha.continuousOn.matrixBilinearForm.mono hCA)
  have haBound : ∀ z ∈ e.target, ∀ v w : X N, |dotProduct v ((a z).mulVec w)| ≤
      max L 0 * ‖v‖ * ‖w‖ := by
    intro z hz v w
    rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
    have h0 := (matrixBilinearForm (a z)).le_opNorm₂ v w
    exact h0.trans (by gcongr; exact (hL z (hT hz)).trans (le_max_left _ _))
  let U : Opens (X N) := ⟨e.target,e.open_target⟩
  have hm : MemLp (fun z => energyIntegrand (a z) 0 0) ⊤
      ((volume : Measure (X N)).restrict U) :=
    memLp_energyIntegrand_of_bounds (le_max_right L 0)
      ((ha.continuousOn.mono (hT.trans hCA)).aestronglyMeasurable e.open_target.measurableSet)
      (continuous_const.aestronglyMeasurable) (continuous_const.aestronglyMeasurable)
      haBound (fun _ _ => norm_zero.le) (fun _ _ => norm_zero.le)
  have hEq : (fun z => energyIntegrand (a z) 0 0) =ᵐ[(volume : Measure (X N)).restrict U]
      (fun z => energyIntegrand (chartDivergenceMatrix D.metric e z) 0 0) := by
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    exact congrArg (fun a => energyIntegrand a 0 0)
      (chartDivergenceMatrix_eq_signed D e (hMetric (show z ∈ e.target from hz))).symm
  exact (memLp_congr_ae hEq).mp hm

set_option maxHeartbeats 1000000 in
/-- On an open portion of a signed normal chart with compact closure,
the native completion has an actual Sobolev reading with its
divergence equation. The smooth dense tests read in one compact
signed extension, with genuine zero value at every flat face point. -/
theorem NativeBoundaryMetricChart.exists_sobolev_reading_in_signed_region (D : DirichletData m M)
    {p : M} (A : NativeBoundaryMetricChart D.metric p) {W C : Set (X N)}
    (hW : IsOpen W) (hC : IsCompact C) (hCn : C.Nonempty) (hCA : C ⊆ A.ambient)
    (hWA : W ⊆ A.ambient) (hWC : W ∩ positiveHalfSpace N ⊆ C) (hAE : W ∩ positiveHalfSpace N =ᵐ[volume] C) :
    ∃ e : OpenPartialHomeomorph M (X N), e.target = W ∩ positiveHalfSpace N ∧
      (e.symm : X N → M) = A.coord.symm ∧
      ∃ F : DirichletHilbert D →L[ℝ]
          W1p (volume : Measure (X N)) ⟨e.target,e.open_target⟩ 2,
        (∀ w : DirichletHilbert D,
          (W1p.value (F w) : X N → ℝ) =ᵐ[(volume : Measure (X N)).restrict e.target]
          (D.l2Value w : M → ℝ) ∘ e.symm) ∧
        (∀ u : DirichletTest D,
          (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ) =ᵐ[(volume : Measure (X N)).restrict e.target]
            u ∘ e.symm) ∧
        (∀ u : DirichletTest D, ∃ v : X N → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
          EqOn (u ∘ e.symm) v (C ∩ inwardHalfSpace N) ∧
          (∀ z ∈ C, z 0 = 0 → v z = 0)) ∧
        (∀ (f : Lp ℝ 2 D.volume) {q : M → ℝ}, ContinuousOn q e.source → (f : M → ℝ) =ᵐ[D.volume.restrict e.source] q →
          ∀ φ : 𝓓(⟨e.target,e.open_target⟩, ℝ),
            energyFormH1 (fun z => Matrix.of (divergenceCoeff A.field z)) 0 0 (F (D.weakDirichletInverse f))
              (W1p.ofTestFunctionₗ volume ⟨e.target,e.open_target⟩ 2 φ) =
            ∫ z in e.target, (q (e.symm z) * chartVolume A.field z) * φ z) := by
  obtain ⟨e,heT,_,heInv,heI,he,hes,hMetric⟩ :=
    A.exists_interior_restriction hW hWA
  have heC : e.target ⊆ C := heT.symm ▸ hWC
  have hE : e.target ⊆ C ∩ inwardHalfSpace N := by
    intro z hz
    refine ⟨heC hz, ?_⟩
    exact positiveHalfSpace_subset_inwardHalfSpace ((heT ▸ hz).2)
  have hRepr (u : DirichletTest D) : ∃ v : X N → ℝ,
      ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ EqOn (u ∘ e.symm) v (C ∩ inwardHalfSpace N) ∧
        (∀ z ∈ C, z 0 = 0 → v z = 0) := by
    obtain ⟨v,V,hv,hV,hCV,hVA,hvE⟩ := A.exists_smooth_function_extension u.smooth hC hCA
    obtain ⟨χ,hχ,_,hχ1,hχsupp,_⟩ := hC.exists_contDiff_cutoff hV hCV
    let v₁ (z : X N) := χ z * v z
    have hV₁ : EqOn (u ∘ e.symm) v₁ (C ∩ inwardHalfSpace N) := by
      intro z hz
      have hχz : χ z = 1 := mem_singleton_iff.mp
        (interior_subset (hχ1 hz.1) : z ∈ χ ⁻¹' {1})
      have hvz := hvE (show z ∈ V ∩ inwardHalfSpace N from ⟨hCV hz.1,hz.2⟩)
      change (u : M → ℝ) (e.symm z) = χ z * v z
      rw [hχz,one_mul,hvz,Function.comp_apply,heInv]
    refine ⟨v₁,hχ.mul hv,hχsupp.mul_right,hV₁,?_⟩
    intro z hz hz₀
    have hzH : z ∈ inwardHalfSpace N := mem_inwardHalfSpace.mpr hz₀.ge
    have hzT : z ∈ A.coord.target := A.target_eq.symm ▸ ⟨hCA hz,hzH⟩
    have hzs := A.coord.map_target hzT
    have hzb : A.coord.symm z ∈ (J).boundary M := by
      rw [← (J).compl_interior,mem_compl_iff, A.interior_iff _ hzs,A.coord.right_inv hzT]
      rw [mem_positiveHalfSpace,hz₀]
      exact lt_irrefl _
    rw [← hV₁ ⟨hz,hzH⟩,Function.comp_apply,heInv]
    exact u.zero_trace hzb
  have hR (u : DirichletTest D) : ∃ v : X N → ℝ,
      ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ EqOn (u ∘ e.symm) v e.target := by
    obtain ⟨v,hv,hvs,hvE,_⟩ := hRepr u
    exact ⟨v,hv,hvs,hvE.mono hE⟩
  obtain ⟨F,hF⟩ := exists_dirichletHilbert_chartSobolev D e heI he hes hC hCn hCA
    heC (heT.symm ▸ hAE) A.smooth_field hMetric hR
  refine ⟨e,heT,heInv,F,dirichletHilbert_chartSobolev_value D e heI he hes F hF,hF,hRepr,?_⟩
  intro f q hq hf φ
  have h := chartSobolev_weakDirichletInverse_test_of_local D e heI he hes F hF
    (fun u => (hR u).imp fun _ h => ⟨h.1,h.2.2⟩)
    (normalChart_coeff_memLp D A e hC hCA heC hMetric) f hq hf φ
  rw [energyFormH1_def] at h ⊢
  refine _root_.Eq.trans (integral_congr_ae ?_) (h.trans (integral_congr_ae ?_))
  · filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    exact congrArg (fun a => energyIntegrand a 0 0 _ _)
      (chartDivergenceMatrix_eq_signed D e (hMetric (show z ∈ e.target from hz))).symm
  · filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    exact congrArg (fun a : Mat N => q (e.symm z) * Real.sqrt a.det * φ z) (hMetric hz)

/-- Local forcing on a smaller chart whose signed region is
contained in the same compact comparison set. -/
theorem NativeBoundaryMetricChart.exists_sobolev_reading_of_local (D : DirichletData m M)
    {p : M} (A : NativeBoundaryMetricChart D.metric p) {W C : Set (X N)}
    (hW : IsOpen W) (hC : IsCompact C) (hCn : C.Nonempty) (hCA : C ⊆ A.ambient)
    (hWC : W ⊆ C) (hAE : W ∩ positiveHalfSpace N =ᵐ[volume] C) :
    ∃ e : OpenPartialHomeomorph M (X N), e.target = W ∩ positiveHalfSpace N ∧
      (e.symm : X N → M) = A.coord.symm ∧
      ∃ F : DirichletHilbert D →L[ℝ]
          W1p (volume : Measure (X N)) ⟨e.target,e.open_target⟩ 2,
        (∀ w : DirichletHilbert D,
          (W1p.value (F w) : X N → ℝ) =ᵐ[(volume : Measure (X N)).restrict e.target]
          (D.l2Value w : M → ℝ) ∘ e.symm) ∧
        (∀ u : DirichletTest D,
          (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ) =ᵐ[(volume : Measure (X N)).restrict e.target]
            u ∘ e.symm) ∧
        (∀ u : DirichletTest D, ∃ v : X N → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
          EqOn (u ∘ e.symm) v (C ∩ inwardHalfSpace N) ∧
          (∀ z ∈ C, z 0 = 0 → v z = 0)) ∧
        (∀ (f : Lp ℝ 2 D.volume) {q : M → ℝ}, ContinuousOn q e.source → (f : M → ℝ) =ᵐ[D.volume.restrict e.source] q →
          ∀ φ : 𝓓(⟨e.target,e.open_target⟩, ℝ),
            energyFormH1 (fun z => Matrix.of (divergenceCoeff A.field z)) 0 0 (F (D.weakDirichletInverse f))
              (W1p.ofTestFunctionₗ volume ⟨e.target,e.open_target⟩ 2 φ) =
            ∫ z in e.target, (q (e.symm z) * chartVolume A.field z) * φ z) :=
  A.exists_sobolev_reading_in_signed_region D hW hC hCn hCA (hWC.trans hCA)
    (inter_subset_left.trans hWC) hAE

set_option maxHeartbeats 1000000 in
/-- On an open portion of a signed normal chart with compact closure,
the native completion has an actual Sobolev reading with its
divergence equation. The smooth dense tests read in one compact
signed extension, with genuine zero value at every flat face point. -/
theorem NativeBoundaryMetricChart.exists_sobolev_reading (D : DirichletData m M)
    {p : M} (A : NativeBoundaryMetricChart D.metric p) {W C : Set (X N)}
    (hW : IsOpen W) (hC : IsCompact C) (hCn : C.Nonempty) (hCA : C ⊆ A.ambient)
    (hWC : W ⊆ C) (hAE : W ∩ positiveHalfSpace N =ᵐ[volume] C) :
    ∃ e : OpenPartialHomeomorph M (X N), e.target = W ∩ positiveHalfSpace N ∧
      (e.symm : X N → M) = A.coord.symm ∧
      ∃ F : DirichletHilbert D →L[ℝ]
          W1p (volume : Measure (X N)) ⟨e.target,e.open_target⟩ 2,
        (∀ w : DirichletHilbert D,
          (W1p.value (F w) : X N → ℝ) =ᵐ[(volume : Measure (X N)).restrict e.target]
          (D.l2Value w : M → ℝ) ∘ e.symm) ∧
        (∀ u : DirichletTest D, ∃ v : X N → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
          EqOn (u ∘ e.symm) v (C ∩ inwardHalfSpace N) ∧
          (∀ z ∈ C, z 0 = 0 → v z = 0)) ∧
        (∀ (f : Lp ℝ 2 D.volume) {q : M → ℝ}, Continuous q → (f : M → ℝ) =ᵐ[D.volume] q →
          ∀ φ : 𝓓(⟨e.target,e.open_target⟩, ℝ),
            energyFormH1 (fun z => Matrix.of (divergenceCoeff A.field z)) 0 0 (F (D.weakDirichletInverse f))
              (W1p.ofTestFunctionₗ volume ⟨e.target,e.open_target⟩ 2 φ) =
            ∫ z in e.target, (q (e.symm z) * chartVolume A.field z) * φ z) := by
  obtain ⟨e,he,heInv,F,hF,_,hRepr,hEq⟩ := A.exists_sobolev_reading_of_local D hW hC hCn hCA hWC hAE
  refine ⟨e,he,heInv,F,hF,hRepr,?_⟩
  intro f q hq hf φ
  exact hEq f hq.continuousOn (ae_restrict_of_ae hf) φ

end CalderonPatch
