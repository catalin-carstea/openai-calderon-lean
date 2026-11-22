module

public import Proof.CalderonN.UniversalMetricSprayJets

import Proof.CalderonN.CenterJetCalculus
import Proof.CalderonN.LocalJetEnvelopeBounds
import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! Uniform finite spray jets, adapted from the checked Proposition 5.3
release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def backgroundAllMetricJetBudget {m : ℕ} (M : Fin (m+1) → ℝ) : ℝ :=
  1+∑ j, |M j|

theorem backgroundAllMetricJetBudget_ge_one {m : ℕ} (M : Fin (m+1) → ℝ) :
    1 ≤ backgroundAllMetricJetBudget M :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem abs_metricJet_le_all_budget {m : ℕ} (M : Fin (m+1) → ℝ) (j : Fin (m+1)) :
    |M j| ≤ backgroundAllMetricJetBudget M :=
  (Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (le_add_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1))

private theorem Background.reference_matrix_jet_bound {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField dim} {e : Frame dim}
    (h : Background Ω K M g g₁ g₂ e) (j : Fin (m+1)) {x : X dim} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ j.val g x‖ ≤ |M j| := by
  have hg : ContDiffAt ℝ ∞ g x := contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr
    (fun k => (h.1.1 i k).contDiffAt (hΩ.mem_nhds hx)))
  apply norm_iteratedFDeriv_matrix_le_of_entries g x j.val hg (abs_nonneg _)
  intro i k
  exact (h.2.2.2.2.1 g (by simp) j i k x hx).trans (le_abs_self _)

private theorem norm_iteratedFDeriv_clm_le_one {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] (L : P →L[ℝ] Q) (hL : ‖L‖ ≤ 1)
    (p : P) (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n L p‖ ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hD : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
    rw [hD]
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hL
    | succ n => simp [iteratedFDeriv_succ_const]

@[expose] def metricSprayInput (g : (MetricField dim)) (p : (X dim) × (X dim)) : MetricSprayInput dim :=
  (g p.1,(fderiv ℝ g p.1,p.2))

lemma contDiffAt_metricSprayInput (g : (MetricField dim)) (p : (X dim) × (X dim))
    (hg : ContDiffAt ℝ ∞ g p.1) : ContDiffAt ℝ ∞ (metricSprayInput g) p :=
  (hg.comp p contDiffAt_fst).prodMk
    (((hg.fderiv_right (m:=∞) (by simp)).comp p contDiffAt_fst).prodMk contDiffAt_snd)

theorem Background.metricSprayInput_jet_bound {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (h : Background Ω K M g g₁ g₂ e) (N : ℕ) (hNm : N+1 ≤ m)
    {p : (X dim) × (X dim)} (hp : p.1 ∈ Ω) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (metricSprayInput g) p‖ ≤
      ((N.factorial:ℝ)*backgroundAllMetricJetBudget M+1)^n := by
  let B := backgroundAllMetricJetBudget M
  let D := (N.factorial:ℝ)*B+1
  let pi : ((X dim) × (X dim)) →L[ℝ] (X dim) := ContinuousLinearMap.fst ℝ (X dim) (X dim)
  have hpi : ‖pi‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.1‖ ≤ 1*‖q‖
    simpa only [one_mul] using norm_fst_le q
  have hB1 : 1 ≤ B := backgroundAllMetricJetBudget_ge_one M
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hD1 : 1 ≤ D := by
    have hh : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [D]
    linarith only [hh]
  have hDpow : D ≤ D^n := le_self_pow₀ hD1 (by omega)
  have hg : ContDiffAt ℝ ∞ g p.1 :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (h.1.1 i j).contDiffAt (hΩ.mem_nhds hp)))
  have hDG := hg.fderiv_right (m:=∞) (by simp)
  have hComp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : (X dim) → V) (hf : ContDiffAt ℝ ∞ f p.1)
      (hJets : ∀ j : ℕ, j ≤ n → ‖iteratedFDeriv ℝ j f p.1‖ ≤ B) :
      ‖iteratedFDeriv ℝ n (fun q : (X dim) × (X dim) => f q.1) p‖ ≤ D^n := by
    have ht := norm_iteratedFDeriv_comp_at_le (pi : (X dim) × (X dim) → (X dim)) f p n pi.contDiff.contDiffAt hf
      B 1 hJets (fun j hj _ => by
        simpa only [one_pow] using norm_iteratedFDeriv_clm_le_one pi hpi p j hj)
    change ‖iteratedFDeriv ℝ n (fun q : (X dim) × (X dim) => f q.1) p‖ ≤ (n.factorial:ℝ)*B*1^n at ht
    simp only [one_pow,mul_one] at ht
    exact ht.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hnN) hB0).trans
      ((by dsimp only [D];linarith : (N.factorial:ℝ)*B ≤ D).trans hDpow))
  have hA : ContDiffAt ℝ ∞ (fun q : (X dim) × (X dim) => g q.1) p := hg.comp p contDiffAt_fst
  have hDA : ContDiffAt ℝ ∞ (fun q : (X dim) × (X dim) => fderiv ℝ g q.1) p := hDG.comp p contDiffAt_fst
  have hV : ContDiffAt ℝ ∞ (fun q : (X dim) × (X dim) => q.2) p := contDiffAt_snd
  change ‖iteratedFDeriv ℝ n (fun q : (X dim) × (X dim) => (g q.1,(fderiv ℝ g q.1,q.2))) p‖ ≤ D^n
  rw [iteratedFDeriv_prodMk hA (hDA.prodMk hV) (i:=n) (by simp),
    ContinuousMultilinearMap.opNorm_prod,iteratedFDeriv_prodMk hDA hV (i:=n) (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  refine max_le ?_ (max_le ?_ ?_)
  · apply hComp g hg
    intro j hj
    exact (h.reference_matrix_jet_bound hΩ ⟨j,by omega⟩ hp).trans (abs_metricJet_le_all_budget M _)
  · apply hComp (fderiv ℝ g) hDG
    intro j hj
    rw [norm_iteratedFDeriv_fderiv]
    exact (h.reference_matrix_jet_bound hΩ ⟨j+1,by omega⟩ hp).trans (abs_metricJet_le_all_budget M _)
  · have hL : ‖(ContinuousLinearMap.snd ℝ (X dim) (X dim))‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro q
      change ‖q.2‖ ≤ 1*‖q‖
      simpa only [one_mul] using norm_snd_le q
    exact (norm_iteratedFDeriv_clm_le_one (ContinuousLinearMap.snd ℝ (X dim) (X dim)) hL p n hn).trans (one_le_pow₀ hD1)

theorem Background.metricSprayInput_mem {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField dim} {e : Frame dim}
    (h : Background Ω K M g g₁ g₂ e) (hm : 1 ≤ m)
    {x : X dim} (hx : x ∈ Ω) {v : X dim} (hv : ‖v‖ ≤ K) :
    metricSprayInput g (x,v) ∈ universalMetricSpraySet dim K (backgroundAllMetricJetBudget M) := by
  let B := backgroundAllMetricJetBudget M
  have hG0 : ‖g x‖ ≤ B := by
    simpa only [norm_iteratedFDeriv_zero] using
      (h.reference_matrix_jet_bound hΩ ⟨0,by omega⟩ hx).trans (abs_metricJet_le_all_budget M _)
  have hG1 : ‖fderiv ℝ g x‖ ≤ B := by
    rw [← norm_iteratedFDeriv_one]
    exact (h.reference_matrix_jet_bound hΩ ⟨1,by omega⟩ hx).trans (abs_metricJet_le_all_budget M _)
  simp only [universalMetricSpraySet,ellipticMatrixLocus,mem_prod,mem_inter_iff,mem_setOf_eq,metricSprayInput]
  exact ⟨⟨by simpa only [mem_closedBall,dist_zero_right] using hG0, (h.1.2 x hx).1,
      fun w => ((h.1.2 x hx).2 w).1⟩,
      by simpa only [mem_closedBall,dist_zero_right] using hG1,
      by simpa only [mem_closedBall,dist_zero_right] using hv⟩

/-- Uniform finite spray jets for every admitted background metric.
    Only one additional metric derivative is needed. -/
theorem uniform_background_spray_jet_bounds {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    (K : ℝ) (hK : 0 < K) {m : ℕ} (M : Fin (m+1) → ℝ)
    (N : ℕ) (hNm : N+1 ≤ m) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ (g g₁ g₂ : (MetricField dim)) (e : (Frame dim)),
      Background Ω K M g g₁ g₂ e → ∀ x ∈ Ω, ∀ v : (X dim), ‖v‖ ≤ K →
      ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖iteratedFDeriv ℝ n (coordinateGeodesicSpray g) (x,v)‖ ≤ S := by
  let B := backgroundAllMetricJetBudget M
  let D := (N.factorial:ℝ)*B+1
  have hB1 : 1 ≤ B := backgroundAllMetricJetBudget_ge_one M
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hD1 : 1 ≤ D := by
    have hh : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [D]
    linarith only [hh]
  obtain ⟨C,hC,hUniversal⟩ := exists_universalMetricSpray_jet_bound (dim:=dim) K B hK N
  let S := 1+(N.factorial:ℝ)*C*D^N
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hS : 1 ≤ S := by
    have hh : 0 ≤ (N.factorial:ℝ)*C*D^N := by positivity
    dsimp only [S]
    linarith only [hh]
  refine ⟨S,hS,?_⟩
  intro g g₁ g₂ e h x hx v hv n hn hnN
  have hg (z : (X dim)) (hz : z ∈ Ω) : ContDiffAt ℝ ∞ g z :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (h.1.1 i j).contDiffAt (hΩ.mem_nhds hz)))
  have hInput := contDiffAt_metricSprayInput g (x,v) (hg x hx)
  have hDet : (g x).det ≠ 0 := (h.1.posDef hK hx).det_pos.ne'
  have hOuter := contDiffAt_universalMetricSpray (metricSprayInput g (x,v)) hDet
  have hNorm (j : Fin (m+1)) := h.reference_matrix_jet_bound hΩ j hx
  have hG0 : ‖g x‖ ≤ B := by
    simpa only [norm_iteratedFDeriv_zero] using
      (hNorm ⟨0,by omega⟩).trans (abs_metricJet_le_all_budget M _)
  have hG1 : ‖fderiv ℝ g x‖ ≤ B := by
    rw [← norm_iteratedFDeriv_one]
    exact (hNorm ⟨1,by omega⟩).trans (abs_metricJet_le_all_budget M _)
  have hMem : metricSprayInput g (x,v) ∈ universalMetricSpraySet dim K B := by
    simp only [universalMetricSpraySet,ellipticMatrixLocus,mem_prod,mem_inter_iff,mem_setOf_eq,metricSprayInput]
    exact ⟨⟨by simpa only [mem_closedBall,dist_zero_right] using hG0, (h.1.2 x hx).1,
      fun w => ((h.1.2 x hx).2 w).1⟩,
      by simpa only [mem_closedBall,dist_zero_right] using hG1,
      by simpa only [mem_closedBall,dist_zero_right] using hv⟩
  have he : universalMetricSpray ∘ metricSprayInput g =ᶠ[𝓝 (x,v)] coordinateGeodesicSpray g := by
    have hNear : ∀ᶠ p : (X dim) × (X dim) in 𝓝 (x,v), p.1 ∈ Ω :=
      continuousAt_fst.eventually (hΩ.mem_nhds hx)
    filter_upwards [hNear] with p hp
    exact universalMetricSpray_actual g p.1 p.2 (hg p.1 hp)
  rw [← (he.iteratedFDeriv ℝ n).eq_of_nhds]
  have hh := norm_iteratedFDeriv_comp_at_le (metricSprayInput g) universalMetricSpray (x,v) n
    hInput hOuter C D
    (fun j hj => hUniversal j (hj.trans hnN) _ hMem)
    (fun j hj hjn => h.metricSprayInput_jet_bound hΩ N hNm hx j hj (hjn.trans hnN))
  have hFac : (n.factorial:ℝ) ≤ (N.factorial:ℝ) := by exact_mod_cast Nat.factorial_le hnN
  have hPow : D^n ≤ D^N := pow_le_pow_right₀ hD1 hnN
  have hCompare : (n.factorial:ℝ)*C*D^n ≤ (N.factorial:ℝ)*C*D^N := by
    gcongr
  exact hh.trans (hCompare.trans (le_add_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1)))

end CalderonN
