module

public import Proof.CalderonPatch.ChartCoercivity
public import Proof.CalderonPatch.BoxPoincare
public import Proof.CalderonPatch.LocalToGlobalPoincare

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.GreenWeak
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold

namespace CalderonPatch

open CalderonN (I X)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "K" => 𝓘(ℝ, X N)
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

private theorem real_volume_pos_of_open_subset {W C : Set (X N)}
    (hW : IsOpen W) (hWn : W.Nonempty) (hWC : W ⊆ C) (hC : IsCompact C) :
    0 < (volume : Measure (X N)).real C :=
  ENNReal.toReal_pos ((hW.measure_pos volume hWn).trans_le (measure_mono hWC)).ne'
    hC.measure_lt_top.ne

private theorem ae_eq_closedBall (x : X N) {r : ℝ} (hr : 0 < r) :
    ball x r =ᵐ[volume] closedBall x r := by
  have h : ∀ᵐ y ∂(volume : Measure (X N)), y ∉ frontier (ball x r) := by
    rw [ae_iff]
    have hfront : {y : X N | ¬ y ∉ frontier (ball x r)} = frontier (ball x r) := by
      ext y
      exact not_not
    rw [hfront]
    exact (convex_ball x r).addHaar_frontier volume
  filter_upwards [h] with y hy
  apply propext
  change y ∈ ball x r ↔ y ∈ closedBall x r
  refine ⟨fun h => ball_subset_closedBall h,fun h => ?_⟩
  rw [frontier,closure_ball x hr.ne',isOpen_ball.interior_eq] at hy
  exact not_not.mp (fun h' => hy ⟨h,h'⟩)

private theorem transfer_chart_estimate {A B L I S E D : ℝ} (hB : 0 < B) (hL : 0 < L)
    (hD : 0 ≤ D) (hA : A ≤ B * I) (hI : I ≤ D * S) (hS : L * S ≤ E) :
    A ≤ (B * D / L) * E := by
  have hS' : S ≤ E / L := (le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hS)
  calc
    A ≤ B * I := hA
    _ ≤ B * (D * S) := mul_le_mul_of_nonneg_left hI hB.le
    _ ≤ B * (D * (E / L)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS' hD) hB.le
    _ = _ := by ring

private theorem exists_interior_local_poincare
    (g : SmoothMetric N M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    {p : M} (hp : p ∈ (J).interior M) :
    ∃ A : Set M, p ∈ A ∧ IsOpen A ∧ ∃ C : ℝ,
      ∀ u : M → ℝ, ContMDiff J R ∞ u → ∃ c : ℝ,
        (∫ x in A, (u x - c)^2 ∂μ) ≤ C * ∫ x, energyPairingDensity g u u x ∂μ := by
  obtain ⟨e,hPe,_,heI,he,hes⟩ := exists_interiorChart p hp isOpen_univ (mem_univ p)
  let q := e p
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hPe))
  let W := ball q (r / 2)
  let C := closedBall q (r / 2)
  have hr2 : 0 < r / 2 := half_pos hr
  have hC : IsCompact C := isCompact_closedBall _ _
  have hCΩ : C ⊆ e.target := (closedBall_subset_ball (half_lt_self hr)).trans hBall
  have hWC : W ⊆ C := ball_subset_closedBall
  let D := nativeInteriorMetricChart g μ hμ e heI he hes
  obtain ⟨A,hS,hT,hInv,_⟩ := restrict_interiorMetricChart D isOpen_ball (hWC.trans hCΩ)
  have hγ : EqOn (coordinateMetric g A.chart) (coordinateMetric g e) A.chart.target := by
    intro x _
    have hInv' : (A.chart.symm : X N → M) = e.symm := hInv
    unfold coordinateMetric
    rw [hInv']
  obtain ⟨L,B,hL,hB,hEst⟩ := exists_native_chart_energy_comparison g μ hμ A.chart
    A.source_interior A.smooth A.smooth_inverse hC hCΩ
    (hT.symm ▸ hWC) (hT.symm ▸ ae_eq_closedBall q hr2) D.smooth_metric hγ
  let D₀ : ℝ := (diam C)^2 * 2^Module.finrank ℝ (X N)
  have hD₀ : 0 ≤ D₀ := by unfold D₀; positivity
  refine ⟨A.chart.source,?_,A.chart.open_source,B * D₀ / L,fun u hu => ?_⟩
  · rw [hS]
    exact ⟨hPe,mem_ball_self hr2⟩
  have hU : ContDiffOn ℝ ∞ (u ∘ e.symm) e.target := (hu.comp_contMDiffOn hes).contDiffOn
  obtain ⟨v,hv,_,U,hUo,hCU,_,hV⟩ :=
    CalderonN.exists_contDiff_extension_near_compact e.open_target hC hCΩ hU
  have hEq : EqOn (u ∘ A.chart.symm) v A.chart.target := by
    have hInv' : (A.chart.symm : X N → M) = e.symm := hInv
    rw [hInv']
    apply hV.symm.mono
    rw [hT]
    exact hWC.trans hCU
  obtain ⟨hSq,hDif⟩ := hEst hu hv hEq
  have hM := real_volume_pos_of_open_subset isOpen_ball (nonempty_ball.mpr hr2) hWC hC
  have hDiam (x : X N) (hx : x ∈ C) (y : X N) (hy : y ∈ C) : ‖y - x‖ ≤ diam C := by
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem hC.isBounded hy hx
  let c := (∫ x in C, v x) / (volume : Measure (X N)).real C
  refine ⟨c, transfer_chart_estimate hB hL hD₀ (hSq c) ?_ hDif⟩
  exact integral_sq_sub_average_le_of_convex volume hC (convex_closedBall _ _) hM hDiam
    (hv.of_le (by simp))

private theorem NativeBoundaryMetricChart.exists_local_poincare
    (g : SmoothMetric N M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    {p : M} (D : NativeBoundaryMetricChart g p) :
    ∃ A : Set M, p ∈ A ∧ IsOpen A ∧ ∃ C₁ C₂ : ℝ,
      (∀ u : M → ℝ, ContMDiff J R ∞ u → ∃ c : ℝ,
        (∫ x in A, (u x - c)^2 ∂μ) ≤ C₁ * ∫ x, energyPairingDensity g u u x ∂μ) ∧
      ∀ u : M → ℝ, ContMDiff J R ∞ u → EqOn u 0 ((J).boundary M) →
        (∫ x in A, (u x)^2 ∂μ) ≤ C₂ * ∫ x, energyPairingDensity g u u x ∂μ := by
  obtain ⟨a,b,hab,ha,hb,hp,hBox⟩ := D.exists_normalHalfBox
  let A := D.coord.source ∩ D.coord ⁻¹' normalHalfBox a b
  let ℓ := MeasurableEquiv.toLp 2 (I N → ℝ)
  let C := ℓ '' Icc a b
  let Q := univ.pi (fun i : I N => Ioo (a i) (b i))
  let W : Set (X N) := ℓ.symm ⁻¹' Q
  have hℓ : Continuous (ℓ : (I N → ℝ) → X N) := PiLp.continuous_toLp 2 _
  have hC : IsCompact C := isCompact_Icc.image hℓ
  have hCD : C ⊆ D.ambient := image_subset_iff.mpr hBox
  have hW : IsOpen W := (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).preimage
    (PiLp.continuous_ofLp 2 (fun _ : I N => ℝ))
  have hCeq : C = ℓ.symm ⁻¹' Icc a b := ℓ.toEquiv.image_eq_preimage_symm _
  have hWC : W ⊆ C := by
    rw [hCeq]
    intro x hx
    have hh := mem_pi.mp hx
    exact ⟨fun i => (hh i (mem_univ i)).1.le,fun i => (hh i (mem_univ i)).2.le⟩
  have hAE : W =ᵐ[volume] C := by
    rw [hCeq]
    exact (PiLp.volume_preserving_ofLp (I N)).quasiMeasurePreserving.preimage_ae_eq
      Measure.univ_pi_Ioo_ae_eq_Icc
  have hWpos : W ⊆ positiveHalfSpace N := by
    intro x hx
    have h := (mem_pi.mp hx 0 (mem_univ 0)).1
    exact (mem_positiveHalfSpace).mpr (ha ▸ h)
  obtain ⟨e,heT,heF,heInv,heI,he,hes,hMetric⟩ := D.exists_interior_restriction hW
    (hWC.trans hCD)
  have hT : e.target = W := heT.trans (inter_eq_left.mpr hWpos)
  have hAeq : A ∩ (J).interior M = e.source := by
    ext x
    constructor
    · rintro ⟨⟨hxs,hxbox⟩,hxI⟩
      have hxp := (D.interior_iff x hxs).mp hxI
      have hxW : D.coord x ∈ W := by
        apply Set.mem_pi.mpr
        intro i _
        change a i < D.coord x i ∧ D.coord x i < b i
        refine ⟨?_,hxbox.2.1 i⟩
        by_cases hi : i = 0
        · subst i
          exact ha.symm ▸ mem_positiveHalfSpace.mp hxp
        · exact hxbox.2.2 i hi
      have hh := e.map_target (hT.symm ▸ hxW)
      rwa [heInv,D.coord.left_inv hxs] at hh
    · intro hx
      have hxp := e.map_source hx
      rw [hT] at hxp
      have hxd : e x ∈ D.coord.target := D.target_eq.symm ▸
        ⟨hCD (hWC hxp),positiveHalfSpace_subset_inwardHalfSpace (hWpos hxp)⟩
      have hs := D.coord.map_target hxd
      have heq := e.left_inv hx
      rw [heInv] at heq
      rw [heq] at hs
      have hCoord : D.coord x = e x := (congrFun heF x).symm
      rw [← hCoord] at hxp
      have hn := mem_pi.mp hxp
      exact ⟨⟨hs, ⟨(mem_positiveHalfSpace.mp (hWpos hxp)).le,
        fun i => (hn i (mem_univ i)).2,fun i _ => (hn i (mem_univ i)).1⟩⟩,heI hx⟩
  have hI : ∀ᵐ x ∂μ, x ∈ (J).interior M := by
    rw [ae_iff]
    change μ (((J).interior M)ᶜ) = 0
    rw [(J).compl_interior]
    exact metricVolume_boundary_eq_zero g μ hμ
  have hEqA : A =ᵐ[μ] e.source := by
    filter_upwards [hI] with x hx
    apply propext
    rw [← hAeq]
    simp only [mem_inter_iff,hx,and_true]
  have hM : 0 < (volume : Measure (X N)).real C := by
    apply real_volume_pos_of_open_subset hW _ hWC hC
    refine ⟨ℓ (fun i => (a i + b i) / 2),?_⟩
    change ℓ.symm (ℓ (fun i => (a i + b i) / 2)) ∈ Q
    rw [ℓ.symm_apply_apply]
    apply Set.mem_pi.mpr
    intro i _
    have hi : a i < b i := by
      by_cases h : i = 0
      · skip
        rw [h,ha]
        exact hb
      · exact (hp.2.2 i h).trans (hp.2.1 i)
    exact ⟨by linarith,by linarith⟩
  have hD (x : X N) (hx : x ∈ C) (y : X N) (hy : y ∈ C) : ‖y - x‖ ≤ diam C := by
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem hC.isBounded hy hx
  have hConv : Convex ℝ C := (convex_Icc a b).linear_image
    (WithLp.linearEquiv 2 ℝ (I N → ℝ)).symm.toLinearMap
  obtain ⟨L,B,hL,hB,hEst⟩ := exists_native_chart_energy_comparison g μ hμ e heI he hes
    hC hCD (hT.symm ▸ hWC) (hT.symm ▸ hAE) D.smooth_field hMetric
  let D₀ : ℝ := (diam C)^2 * 2^Module.finrank ℝ (X N)
  have hD₀ : 0 ≤ D₀ := by unfold D₀; positivity
  have hExt {u : M → ℝ} (hu : ContMDiff J R ∞ u) :
      ∃ v : X N → ℝ, ContDiff ℝ ∞ v ∧ EqOn v (u ∘ D.coord.symm) (C ∩ H) ∧
        EqOn (u ∘ e.symm) v e.target := by
    obtain ⟨v,U,hv,_,hCU,_,hU⟩ := D.exists_smooth_function_extension hu hC hCD
    refine ⟨v,hv,hU.mono (inter_subset_inter_left H hCU),?_⟩
    rw [heInv,hT]
    exact hU.symm.mono (subset_inter (hWC.trans hCU)
      (hWpos.trans positiveHalfSpace_subset_inwardHalfSpace))
  refine ⟨A,⟨D.point_source,hp⟩,D.isOpen_preimage_normalHalfBox a b,
    B * D₀ / L,B * (b 0)^2 / L,?_,?_⟩
  · intro u hu
    obtain ⟨v,hv,_,hRepr⟩ := hExt hu
    obtain ⟨hSq,hDif⟩ := hEst hu hv hRepr
    let c := (∫ x in C, v x) / (volume : Measure (X N)).real C
    refine ⟨c,?_⟩
    rw [setIntegral_congr_set hEqA]
    exact transfer_chart_estimate hB hL hD₀ (hSq c)
      (integral_sq_sub_average_le_of_convex volume hC hConv hM hD (hv.of_le (by simp))) hDif
  · intro u hu hTrace
    obtain ⟨v,hv,hCRepr,hRepr⟩ := hExt hu
    obtain ⟨hSq,hDif⟩ := hEst hu hv hRepr
    have hZero : EqOn (fun z => v (WithLp.toLp 2 (Fin.insertNth 0 0 z))) 0
        (Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)) := by
      intro z hz
      let x := ℓ (Fin.insertNth 0 0 z)
      have hxC : x ∈ C := mem_image_of_mem ℓ (insertNth_mem_box 0 ⟨ha.le,hb.le⟩ hz)
      have hx0 : x 0 = 0 := by simp [x,ℓ]
      have hxH : x ∈ H := (mem_inwardHalfSpace).mpr hx0.ge
      have hxT : x ∈ D.coord.target := D.target_eq.symm ▸ ⟨hCD hxC,hxH⟩
      have hxB : D.coord.symm x ∈ (J).boundary M := by
        rw [← (J).compl_interior]
        intro hi
        have hh := (D.interior_iff _ (D.coord.map_target hxT)).mp hi
        rw [D.coord.right_inv hxT] at hh
        exact ((mem_positiveHalfSpace.mp hh).ne') hx0
      exact (hCRepr ⟨hxC,hxH⟩).trans (hTrace hxB)
    have hEu := integral_sq_le_height_sq_integral_fderiv_of_box_zero_trace hab ha (hv.of_le (by simp)) hZero
    have hLp (f : X N → ℝ) : (∫ x in C, f x) = ∫ y in Icc a b, f (ℓ y) :=
      (PiLp.volume_preserving_toLp (I N)).setIntegral_image_emb ℓ.measurableEmbedding f _
    have hEu' : (∫ x in C, (v x)^2) ≤ (b 0)^2 * ∫ x in C, ‖fderiv ℝ v x‖^2 := by
      simp only [hLp]
      exact hEu
    rw [setIntegral_congr_set hEqA]
    exact transfer_chart_estimate hB hL (sq_nonneg _) (by simpa only [sub_zero] using hSq 0)
      hEu' hDif

/-- On a connected compact manifold with nonempty boundary, the
native gradient energy controls the squared integral of every smooth
zero-trace function. -/
theorem exists_dirichlet_poincare_constant [PreconnectedSpace M]
    (g : SmoothMetric N M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    (hBoundary : ((J).boundary M).Nonempty) :
    ∃ C : ℝ, ∀ u : M → ℝ, ContMDiff J R ∞ u → EqOn u 0 ((J).boundary M) →
      (∫ x, (u x)^2 ∂μ) ≤ C * ∫ x, energyPairingDensity g u u x ∂μ := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  let : μ.IsOpenPosMeasure := ⟨fun U hU hUn => (hμ.measure_pos_of_open_nonempty hU hUn).ne'⟩
  let P (u : M → ℝ) := ContMDiff J R ∞ u ∧ EqOn u 0 ((J).boundary M)
  let E (u : M → ℝ) := ∫ x, energyPairingDensity g u u x ∂μ
  have hInt (u : M → ℝ) (hu : P u) : AEMeasurable u μ ∧ Integrable (fun x => (u x)^2) μ := by
    refine ⟨hu.1.continuous.measurable.aemeasurable,?_⟩
    exact integrableOn_univ.mp ((hu.1.continuous.pow 2).continuousOn.integrableOn_compact isCompact_univ)
  obtain ⟨p,hp⟩ := hBoundary
  obtain ⟨D⟩ := exists_nativeBoundaryMetricChart g p hp
  obtain ⟨A,hpA,hA,_,C₀,_,hAnchor⟩ := D.exists_local_poincare g μ hμ
  have hLocal (q : M) : ∃ V : Set M, q ∈ V ∧ IsOpen V ∧ ∃ C : ℝ,
      ∀ u, P u → ∃ c : ℝ, (∫ x in V, (u x - c)^2 ∂μ) ≤ C * E u := by
    by_cases hq : q ∈ (J).interior M
    · obtain ⟨V,hqV,hV,C,h⟩ := exists_interior_local_poincare g μ hμ hq
      exact ⟨V,hqV,hV,C,fun u hu => h u hu.1⟩
    · have hqb : q ∈ (J).boundary M := by rw [← (J).compl_interior]; exact hq
      obtain ⟨G⟩ := exists_nativeBoundaryMetricChart g q hqb
      obtain ⟨V,hqV,hV,C,_,h,_⟩ := G.exists_local_poincare g μ hμ
      exact ⟨V,hqV,hV,C,fun u hu => h u hu.1⟩
  obtain ⟨C,h⟩ := exists_integral_sq_le_of_local_poincare P E hInt hLocal hA ⟨p,hpA⟩ C₀
    (fun u hu => hAnchor u hu.1 hu.2)
  exact ⟨C,fun u hu hTrace => h u ⟨hu,hTrace⟩⟩

end CalderonPatch
