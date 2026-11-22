module

public import Proof.CalderonPatch.DirichletWeak
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Zero
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Restriction

import Proof.CalderonN.GreenRestriction
import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace TauCeti
open scoped ContDiff Distributions ENNReal Gradient Manifold RealInnerProductSpace Topology

namespace CalderonPatch

open CalderonN (X MetricField chartVolume)

variable {n : ℕ}

private def supportedSobolevReading (U : Opens (X n)) (v : X n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    W1p (volume : Measure (X n)) U 2 :=
  W1p.restrictL (le_top : U ≤ (⊤ : Opens (X n)))
    (W1p.ofTestFunctionₗ volume ⊤ 2 ⟨v,hv,hvc,subset_univ _⟩)

private theorem value_supportedSobolevReading (U : Opens (X n)) (v : X n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    (W1p.value (supportedSobolevReading U v hv hvc) : X n → ℝ) =ᵐ[volume.restrict U] v := by
  let φ : 𝓓((⊤ : Opens (X n)), ℝ) := ⟨v,hv,hvc,subset_univ _⟩
  let w := W1p.ofTestFunctionₗ volume ⊤ 2 φ
  have h : (W1p.value w : X n → ℝ) =ᵐ[volume.restrict (⊤ : Opens (X n))] v := by
    unfold w
    rw [W1p.value_ofTestFunctionₗ]
    exact testFunctionLp_apply_ae 2 φ
  exact (W1p.value_restrictL_ae (le_top : U ≤ (⊤ : Opens (X n))) w).trans
    (h.filter_mono (ae_mono (Measure.restrict_mono_set _ (subset_univ _))))

private theorem gradient_supportedSobolevReading (U : Opens (X n)) (v : X n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    (W1p.gradient (supportedSobolevReading U v hv hvc) : X n → X n) =ᵐ[volume.restrict U]
      gradient v := by
  let φ : 𝓓((⊤ : Opens (X n)), ℝ) := ⟨v,hv,hvc,subset_univ _⟩
  let w := W1p.ofTestFunctionₗ volume ⊤ 2 φ
  have h : (W1p.gradient w : X n → X n) =ᵐ[volume.restrict (⊤ : Opens (X n))] gradient v := by
    unfold w
    rw [W1p.gradient_ofTestFunctionₗ]
    exact gradientTestFunctionLp_apply_ae 2 φ
  exact (W1p.gradient_restrictL_ae (le_top : U ≤ (⊤ : Opens (X n))) w).trans
    (h.filter_mono (ae_mono (Measure.restrict_mono_set _ (subset_univ _))))

private theorem norm_supportedSobolevReading_sq (U : Opens (X n)) (v : X n → ℝ)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    ‖supportedSobolevReading U v hv hvc‖^2 = (∫ x in U, (v x)^2) +
      ∫ x in U, ‖fderiv ℝ v x‖^2 := by
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
    ← W1p.integral_value_sq_eq_norm_value_sq, ← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  congr 1
  · apply integral_congr_ae
    filter_upwards [value_supportedSobolevReading U v hv hvc] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [gradient_supportedSobolevReading U v hv hvc] with x hx
    rw [hx,norm_gradient_eq_norm_fderiv]

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "K" => 𝓘(ℝ, X N)
local notation "R" => 𝓘(ℝ, ℝ)

omit [PreconnectedSpace M] in
private theorem exists_coordinate_value_bound (D : DirichletData m M)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {C Ω : Set (X N)} (hC : IsCompact C) (hCn : C.Nonempty) (hCΩ : C ⊆ Ω)
    (heC : e.target ⊆ C) {γ : MetricField N} (hγ : CalderonN.SmoothMetric Ω γ)
    (hMetric : EqOn (coordinateMetric D.metric e) γ e.target) :
    ∃ ρ > 0, ∀ {u : M → ℝ} {v : X N → ℝ}, ContMDiff J R ∞ u → ContDiff ℝ ∞ v →
      EqOn (u ∘ e.symm) v e.target →
      ρ * (∫ x in e.target, (v x)^2) ≤ ∫ x, (u x)^2 ∂D.volume := by
  let : IsFiniteMeasure D.volume := D.metric_volume.isFiniteMeasure
  have hρC : ContinuousOn (chartVolume γ) C :=
    (CalderonN.continuousOn_metricVolumeDensity hγ).mono hCΩ
  obtain ⟨p,hp,hρ⟩ := hC.exists_isMinOn hCn hρC
  let ρ := chartVolume γ p
  have hρ₀ : 0 < ρ := Real.sqrt_pos.mpr (hγ.2 p (hCΩ hp)).det_pos
  refine ⟨ρ,hρ₀,fun {u v} hu hv hRepr => ?_⟩
  let T := nativeInteriorMetricChart D.metric D.volume D.metric_volume e heI he hes
  let w (x : X N) := (v x)^2
  have hw : Continuous w := hv.continuous.pow 2
  have hW : EqOn ((fun x => (u x)^2) ∘ T.chart.symm) w e.target := by
    intro x hx
    exact congrArg (· ^ 2) (hRepr hx)
  have hWρ : ContinuousOn (fun x => w x * chartVolume γ x) C := hw.continuousOn.mul hρC
  have hIntegral : Integrable (fun x => (u x)^2) D.volume :=
    integrableOn_univ.mp ((hu.continuous.pow 2).continuousOn.integrableOn_compact isCompact_univ)
  calc
    _ = ∫ x in e.target, ρ * w x := (integral_const_mul _ _).symm
    _ ≤ ∫ x in e.target, w x * chartVolume γ x := by
      apply setIntegral_mono_on ((hw.const_mul ρ).continuousOn.integrableOn_compact hC |>.mono_set heC)
        ((hWρ.integrableOn_compact hC).mono_set heC) e.open_target.measurableSet
      intro x hx
      rw [mul_comm ρ]
      exact mul_le_mul_of_nonneg_left (hρ (heC hx)) (sq_nonneg _)
    _ = ∫ x in e.target, w x * chartVolume (coordinateMetric D.metric e) x := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro x hx
      simp only [chartVolume,hMetric hx]
    _ = ∫ x in e.source, (u x)^2 ∂D.volume :=
      (integral_interiorChart_of_coordinateRepresentation T hw.continuousOn hW).symm
    _ ≤ _ := setIntegral_le_integral hIntegral (Eventually.of_forall fun _ => sq_nonneg _)

/-- The native energy completion reads continuously in the Tau Ceti
chart `H¹` space. The chart target can meet the boundary of the
compact coefficient region on a null set. -/
theorem exists_dirichletHilbert_chartSobolev (D : DirichletData m M)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {C Ω : Set (X N)} (hC : IsCompact C) (hCn : C.Nonempty) (hCΩ : C ⊆ Ω)
    (heC : e.target ⊆ C) (hAE : e.target =ᵐ[volume] C)
    {γ : MetricField N} (hγ : CalderonN.SmoothMetric Ω γ)
    (hMetric : EqOn (coordinateMetric D.metric e) γ e.target)
    (hRepr : ∀ u : DirichletTest D, ∃ v : X N → ℝ,
      ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ EqOn (u ∘ e.symm) v e.target) :
    let U : Opens (X N) := ⟨e.target,e.open_target⟩
    ∃ F : DirichletHilbert D →L[ℝ] W1p (volume : Measure (X N)) U 2,
      ∀ u : DirichletTest D, (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ)
        =ᵐ[volume.restrict U] u ∘ e.symm := by
  classical
  let U : Opens (X N) := ⟨e.target,e.open_target⟩
  choose v hv hvc hRep using hRepr
  let s (u : DirichletTest D) := supportedSobolevReading U (v u) (hv u) (hvc u)
  have hValue (u : DirichletTest D) : (W1p.value (s u) : X N → ℝ)
      =ᵐ[volume.restrict U] u ∘ e.symm :=
    (value_supportedSobolevReading U (v u) (hv u) (hvc u)).trans
      ((ae_restrict_mem U.isOpen.measurableSet).mono fun _ hx => (hRep u hx).symm)
  let S : DirichletTest D →ₗ[ℝ] W1p (volume : Measure (X N)) U 2 :=
    { toFun := s
      map_add' := fun u w => by
        apply W1p.ext_value
        simp only [← W1p.valueL_apply,map_add]
        apply Lp.ext
        filter_upwards [hValue (u + w),hValue u,hValue w,
          Lp.coeFn_add (W1p.value (s u)) (W1p.value (s w))] with x h₁ h₂ h₃ h₄
        simp only [W1p.valueL_apply,h₁,h₂,h₃,h₄,DirichletTest.coe_add,Function.comp_apply,Pi.add_apply]
      map_smul' := fun c u => by
        apply W1p.ext_value
        simp only [← W1p.valueL_apply,RingHom.id_apply,map_smul]
        apply Lp.ext
        filter_upwards [hValue (c • u),hValue u,Lp.coeFn_smul c (W1p.value (s u))]
          with x h₁ h₂ h₃
        simp only [W1p.valueL_apply,h₁,h₂,h₃,DirichletTest.coe_smul,Function.comp_apply,Pi.smul_apply] }
  obtain ⟨ρ,hρ,hValueBound⟩ := exists_coordinate_value_bound D e heI he hes
    hC hCn hCΩ heC hγ hMetric
  obtain ⟨L,B,hL,_,hEnergy⟩ := exists_native_chart_energy_comparison D.metric D.volume
    D.metric_volume e heI he hes hC hCΩ heC hAE hγ hMetric
  obtain ⟨P,hP⟩ := exists_dirichlet_poincare_constant D.metric D.volume
    D.metric_volume D.boundary_nonempty
  let T := max P 0 / ρ + 1 / L
  have hT : 0 ≤ T := add_nonneg (div_nonneg (le_max_right _ _) hρ.le) (one_div_nonneg.mpr hL.le)
  have hBound : ∃ A : ℝ, ∀ u, ‖S u‖ ≤ A * ‖u‖ := by
    refine ⟨Real.sqrt T,fun u => ?_⟩
    have hP₀ := hP u u.smooth u.zero_trace
    rw [← DirichletTest.inner_eq D,real_inner_self_eq_norm_sq] at hP₀
    have hW := hValueBound u.smooth (hv u) (hRep u)
    have hD := (hEnergy u.smooth (hv u) (hRep u)).2
    rw [← DirichletTest.inner_eq D,real_inner_self_eq_norm_sq,← setIntegral_congr_set hAE] at hD
    have h₁ : (∫ x in U, (v u x)^2) ≤ (max P 0 / ρ) * ‖u‖^2 := by
      change (∫ x in e.target, (v u x)^2) ≤ _
      have hh := hW.trans (hP₀.trans (mul_le_mul_of_nonneg_right (le_max_left P 0) (sq_nonneg _)))
      exact ((le_div_iff₀ hρ).mpr (by simpa only [mul_comm] using hh)).trans_eq (by ring)
    have h₂ : (∫ x in U, ‖fderiv ℝ (v u) x‖^2) ≤ (1 / L) * ‖u‖^2 := by
      change (∫ x in e.target, ‖fderiv ℝ (v u) x‖^2) ≤ _
      exact ((le_div_iff₀ hL).mpr (by simpa only [mul_comm] using hD)).trans_eq (by ring)
    have h₃ : ‖S u‖^2 ≤ T * ‖u‖^2 := by
      change ‖supportedSobolevReading U (v u) (hv u) (hvc u)‖^2 ≤ _
      rw [norm_supportedSobolevReading_sq]
      exact (add_le_add h₁ h₂).trans_eq (by unfold T; ring)
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    rwa [← pow_two,← pow_two,mul_pow,Real.sq_sqrt hT]
  let F := (S.mkContinuousOfExistsBound hBound).fromCompletion
  refine ⟨F, fun u => ?_⟩
  change (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ) =ᵐ[volume.restrict U] u ∘ e.symm
  simp only [F,ContinuousLinearMap.fromCompletion_apply_coe,LinearMap.mkContinuousOfExistsBound_apply]
  exact hValue u

omit [CompactSpace M] [T2Space M] [PreconnectedSpace M] in
private theorem ae_coordinate_of_ae_native (g : SmoothMetric N M)
    (μ : Measure M) (hμ : IsMetricVolume g μ)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {Q : M → Prop} (hQ : ∀ᵐ x ∂μ, Q x) :
    ∀ᵐ z ∂(volume : Measure (X N)).restrict e.target, Q (e.symm z) := by
  let ν := CalderonN.chartVolumeMeasure e.target (coordinateMetric g e)
  have hμe : (μ.restrict e.source).map e = ν := volume_eq_coordinate g μ hμ e heI he hes
  have heM : AEMeasurable (e : M → X N) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hs : AEMeasurable (e.symm : X N → M) (volume.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  have hsν : AEMeasurable (e.symm : X N → M) ν :=
    hs.mono_ac (withDensity_absolutelyContinuous _ _)
  have heId : ((e.symm : X N → M) ∘ e) =ᵐ[μ.restrict e.source] id := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
    exact e.left_inv hx
  have hback : ν.map e.symm = μ.restrict e.source := by
    rw [← hμe, AEMeasurable.map_map_of_aemeasurable (hμe.symm ▸ hsν) heM,
      Measure.map_congr heId, Measure.map_id]
  have hQν : ∀ᵐ z ∂ν, Q (e.symm z) := ae_of_ae_map hsν (hback.symm ▸
    (hQ.filter_mono (ae_mono Measure.restrict_le_self)))
  let γ := coordinateMetric g e
  have hγ := coordinateMetric_smooth g e he hes
  have hρ := (CalderonN.continuousOn_metricVolumeDensity hγ).aemeasurable
    e.open_target.measurableSet (μ := (volume : Measure (X N)))
  dsimp only [ν,CalderonN.chartVolumeMeasure] at hQν
  rw [ae_withDensity_iff' hρ.ennreal_ofReal] at hQν
  filter_upwards [hQν,ae_restrict_mem e.open_target.measurableSet] with z hz hzT
  exact hz (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (hγ.2 z hzT).det_pos)).ne'

/-- A bounded chart reading that agrees on smooth tests reads the
actual completed (L^2) value almost everywhere. -/
theorem dirichletHilbert_chartSobolev_value (D : DirichletData m M)
    (e : OpenPartialHomeomorph M (X N)) (heI : e.source ⊆ (J).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    (F : DirichletHilbert D →L[ℝ] W1p (volume : Measure (X N)) ⟨e.target,e.open_target⟩ 2)
    (hF : ∀ u : DirichletTest D,
      (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ)
        =ᵐ[(volume : Measure (X N)).restrict e.target] u ∘ e.symm)
    (w : DirichletHilbert D) :
    (W1p.value (F w) : X N → ℝ) =ᵐ[(volume : Measure (X N)).restrict e.target]
      (D.l2Value w : M → ℝ) ∘ e.symm := by
  let U : Opens (X N) := ⟨e.target,e.open_target⟩
  let η : DirichletTest D → DirichletHilbert D := (↑)
  have hη : DenseRange η := UniformSpace.Completion.denseRange_coe
  obtain ⟨t, ht, hLim⟩ := mem_closure_iff_seq_limit.mp (hη w)
  choose u hu using ht
  have hLim' : Tendsto (fun k => (u k : DirichletHilbert D)) atTop (𝓝 w) := by
    simpa only [η,hu] using hLim
  have hGlobal : Tendsto (fun k => D.l2Value (u k : DirichletHilbert D)) atTop
      (𝓝 (D.l2Value w)) := D.l2Value.continuous.continuousAt.tendsto.comp hLim'
  have hCont : Continuous (fun w => W1p.value (F w)) :=
    ((W1p.valueL (mu := volume) (Omega := U) (p := 2)).comp F).continuous
  have hLocal : Tendsto (fun k => W1p.value (F (u k : DirichletHilbert D))) atTop
      (𝓝 (W1p.value (F w))) := hCont.continuousAt.tendsto.comp hLim'
  obtain ⟨i,hi,hGi⟩ := (tendstoInMeasure_of_tendsto_Lp hGlobal).exists_seq_tendsto_ae
  obtain ⟨j,hj,hLj⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hLocal.comp hi.tendsto_atTop)).exists_seq_tendsto_ae
  have hA (k : ℕ) : (W1p.value (F (u k : DirichletHilbert D)) : X N → ℝ)
      =ᵐ[(volume : Measure (X N)).restrict e.target]
        (D.l2Value (u k : DirichletHilbert D) : M → ℝ) ∘ e.symm := by
    apply (hF (u k)).trans
    exact ae_coordinate_of_ae_native D.metric D.volume D.metric_volume e heI he hes
      (D.l2Value_coe_ae_eq (u k)).symm
  have hAll := ae_all_iff.mpr hA
  have hGlocal := ae_coordinate_of_ae_native D.metric D.volume D.metric_volume e heI he hes hGi
  filter_upwards [hAll,hGlocal,hLj] with z hAt hGt hLt
  apply tendsto_nhds_unique_of_eventuallyEq hLt (hGt.comp hj.tendsto_atTop)
  exact Eventually.of_forall fun k => hAt (i (j k))

end CalderonPatch
