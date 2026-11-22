module

public import Proof.CalderonN.UniversalParallelCenterJets
public import Proof.CalderonN.UniformNormalMapHigherJets
public import Proof.CalderonN.NormalizedParallelCenterZeroJets
public import Proof.CalderonN.LocalSmoothJetBudget

import Proof.CalderonN.UniformBackgroundSprayJets
import Mathlib.Tactic

/-! Uniform mixed center and velocity jets for the same normalized
parallel-center Jacobian that occurs in the moving trace adjoint. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def actualNormalizedParallelCenterField (g : MetricField dim) (E : X dim × X dim → X dim)
    (p : X dim × X dim) : X dim →L[ℝ] X dim :=
  normalizedParallelCenterJacobian g E p.1 p.2

theorem smoothNear_actualNormalizedParallelCenter
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField dim} (hg : Elliptic Ω K g) (hK : 0 < K)
    {E : X dim × X dim → X dim} {R : X dim → ℝ} (hN : NormalCoordinates Y Ω g E R) :
    smoothNear (actualNormalizedParallelCenterField g E)
      {p | p.1 ∈ Y ∧ p.2 ∈ disk g p.1 (R p.1) ∧
        ‖normalVerticalJacobian E p.1 p.2-ContinuousLinearMap.id ℝ (X dim)‖ < 1} := by
  obtain ⟨U,hU,hPack,hE⟩ := hN.1
  let P := X dim × X dim
  let F (q : P) := (fderiv ℝ E q,metricSprayInput g q)
  let W₀ : Set P := U ∩ Prod.fst ⁻¹' Ω
  have hW₀ : IsOpen W₀ := hU.inter (hΩ.preimage continuous_fst)
  have hDE : ContDiffOn ℝ ∞ (fderiv ℝ E) W₀ :=
    (hE.fderiv_of_isOpen (m:=∞) hU (by simp)).mono inter_subset_left
  let J (q : P) := parallelCenterVerticalInputL (fderiv ℝ E q)
  let W := W₀ ∩ {q : P | ‖J q-ContinuousLinearMap.id ℝ (X dim)‖ < 1}
  have hJ : ContDiffOn ℝ ∞ J W₀ := parallelCenterVerticalInputL.contDiff.comp_contDiffOn hDE
  have hW : IsOpen W := ((hJ.continuousOn.sub continuousOn_const).norm).isOpen_inter_preimage hW₀ isOpen_Iio
  refine ⟨W,hW,?_,?_⟩
  · rintro q ⟨hy,hv,hSmall⟩
    exact ⟨⟨hPack ⟨hy,hv⟩,hN.center_mem hy⟩,hSmall⟩
  · intro q hq
    have hg' (x : X dim) (hx : x ∈ Ω) : ContDiffAt ℝ ∞ g x :=
      contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (hg.1 i j).contDiffAt (hΩ.mem_nhds hx)))
    have hF : ContDiffAt ℝ ∞ F q := (hDE.contDiffAt (hW₀.mem_nhds hq.1)).prodMk
      (contDiffAt_metricSprayInput g q (hg' q.1 hq.1.2))
    have hSmooth := (contDiffAt_universalParallelCenter (F q)
      (hg.posDef hK hq.1.2).det_pos.ne' (invertible_of_near_chartIdentity _ hq.2)).comp q hF
    have hEq : actualNormalizedParallelCenterField g E =ᶠ[𝓝 q] universalParallelCenter ∘ F := by
      filter_upwards [hW₀.mem_nhds hq.1] with p hp
      exact (universalParallelCenter_actual g E p (hg' p.1 hp.2)).symm
    exact (hSmooth.congr_of_eventuallyEq hEq).contDiffWithinAt

theorem uniform_actual_normalizedParallelCenter_jets
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (K : ℝ) (hK : 1 ≤ K)
    {m : ℕ} (N : ℕ) (hm : N+2 ≤ m) (M : Fin (m+1) → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g g₁ g₂ : MetricField dim) (e : Frame dim),
      Background Ω K M g g₁ g₂ e →
      ∀ (E : X dim × X dim → X dim) (R : X dim → ℝ), NormalCoordinates Y Ω g E R →
      ∀ y ∈ Y, ContinuousAt R y → ∀ v : X dim,
        metricPair g y v v < (R y)^2 → ‖v‖ ≤ 1 →
        ‖normalVerticalJacobian E y v-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ) →
        LocalSmoothJetBudget (actualNormalizedParallelCenterField g E) (y,v) N C := by
  have hK' : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨D,hD,hNormal⟩ := uniform_normalMap_higher_jet_bounds hΩ K hK' M (N+1) hm
  let B := backgroundAllMetricJetBudget M
  let D₀ := ((N.factorial:ℝ)*B+1)^N
  let B₀ := max (max B K) D₀
  obtain ⟨S,hS,hOuter⟩ := exists_uniform_universalParallelCenter_jets (dim:=dim) K B D hK' N
  let C := (N.factorial:ℝ)*S*(max D B₀)^N
  have hB : 1 ≤ B := backgroundAllMetricJetBudget_ge_one M
  have hB₀ : 1 ≤ B₀ := (hB.trans (le_max_left _ _)).trans (le_max_left _ _)
  have hC : 0 ≤ C := by
    have hP := zero_le_one.trans hS
    have hQ := (zero_le_one.trans hD).trans (le_max_left D B₀)
    dsimp only [C]
    positivity
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e hbg E R hN y hy hR v hv hv₁ hSmall
  let p : X dim × X dim := (y,v)
  let F (q : X dim × X dim) := (fderiv ℝ E q,metricSprayInput g q)
  have hyΩ := hN.center_mem hy
  have hMem := hbg.metricSprayInput_mem hΩ (by omega : 1 ≤ m) hyΩ (hv₁.trans hK)
  have hgs (x : X dim) (hx : x ∈ Ω) : ContDiffAt ℝ ∞ g x :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (hbg.1.1 i j).contDiffAt (hΩ.mem_nhds hx)))
  obtain ⟨U,hU,hTU,hE⟩ := hN.1
  have hpU : p ∈ U := hTU ⟨hy,hv.le⟩
  have hDE : LocalSmoothJetBudget (fderiv ℝ E) p N D := by
    refine ⟨(hE.contDiffAt (hU.mem_nhds hpU)).fderiv_right (m:=∞) (by simp),fun n hn => ?_⟩
    rw [norm_iteratedFDeriv_fderiv]
    exact (hNormal g g₁ g₂ e hbg Y hY E R hN y hy hR v hv hv₁ (n+1) (by omega) (by omega)).2
  have hInput : LocalSmoothJetBudget (metricSprayInput g) p N B₀ := by
    refine ⟨contDiffAt_metricSprayInput g p (hgs y hyΩ),fun n hn => ?_⟩
    by_cases hn₀ : n = 0
    · subst n
      rw [norm_iteratedFDeriv_zero]
      have ha : ‖g y‖ ≤ B := by
        simpa only [dist_zero_right,mem_closedBall,metricSprayInput,B] using hMem.1.1
      have hda : ‖fderiv ℝ g y‖ ≤ B := by
        simpa only [dist_zero_right,mem_closedBall,metricSprayInput,B] using hMem.2.1
      change max ‖g y‖ (max ‖fderiv ℝ g y‖ ‖v‖) ≤ B₀
      exact (max_le ((ha.trans (le_max_left B K))) (max_le (hda.trans (le_max_left B K))
        ((hv₁.trans hK).trans (le_max_right B K)))).trans (le_max_left _ _)
    · have hc : 1 ≤ (N.factorial:ℝ)*B+1 := le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hB))
      exact (hbg.metricSprayInput_jet_bound hΩ N (by omega) (p:=p) hyΩ n (by omega) hn).trans
        ((pow_le_pow_right₀ hc hn).trans (le_max_right _ _))
  have hF : LocalSmoothJetBudget F p N (max D B₀) := hDE.prod hInput
  have hD₁ : ‖fderiv ℝ E p‖ ≤ D := hDE.value_norm_le
  have hD₀ : ‖parallelCenterVerticalInputL (fderiv ℝ E p)-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ) :=
    hSmall
  have hV : LocalSmoothJetBudget (universalParallelCenter (dim:=dim)) (F p) N S :=
    ⟨contDiffAt_universalParallelCenter (F p) (hbg.1.posDef hK' hyΩ).det_pos.ne'
      (hN.normalVerticalJacobian_isInvertible hy v hv.le), hOuter (F p) hD₁ hD₀ hMem⟩
  have hJ : LocalSmoothJetBudget (universalParallelCenter ∘ F) p N C := hF.comp hV (hD.trans (le_max_left _ _))
  have heq : actualNormalizedParallelCenterField g E =ᶠ[𝓝 p] universalParallelCenter ∘ F := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hΩ.mem_nhds hyΩ)] with q hq
    exact (universalParallelCenter_actual g E q (hgs q.1 hq)).symm
  exact ⟨hJ.smooth.congr_of_eventuallyEq heq,fun n hn => by
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    exact hJ.bound n hn⟩

end CalderonN
