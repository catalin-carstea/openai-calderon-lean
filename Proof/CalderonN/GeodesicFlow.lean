module

public import Proof.CalderonN.GeodesicSpray

import Proof.LocalMetricExtension.ODE.Analysis.ODE.InitialCondition
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff NNReal Topology

namespace CalderonN

variable {dim : ℕ}

private theorem contDiff_infty_globalFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (V : E → E) {L : ℝ≥0} (hL : LipschitzWith L V) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun p : E × ℝ => ODE.globalSolution V hL p.1 p.2) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  exact (ODE.contDiff_globalSolution n V hL (hV.of_le (by simp))).of_le (by exact_mod_cast Nat.le_succ n)

private theorem globalFlow_rest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (V : E → E) {L : ℝ≥0} (hL : LipschitzWith L V)
    {a : E} (ha : V a = 0) (t : ℝ) : ODE.globalSolution V hL a t = a := by
  have hc : (fun _ : ℝ => a) = ODE.globalSolution V hL a := by
    apply ODE.eq_globalSolution
    intro s
    simpa only [ha] using
      (show HasDerivAt (fun _ : ℝ => a) 0 s from hasDerivAt_const _ _)
  exact (congrFun hc t).symm

theorem exists_closedBall_of_compact_zeroSlice {P E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] {K : Set P} (hK : IsCompact K)
    {U : Set (P × E)} (hU : IsOpen U) (hz : K ×ˢ ({0} : Set E) ⊆ U) :
    ∃ r > 0, K ×ˢ closedBall (0 : E) r ⊆ U := by
  obtain ⟨O, V, _, hV, hKO, h0V, hOV⟩ := generalized_tube_lemma hK isCompact_singleton hU hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton _)))
  refine ⟨r / 2, by positivity, fun p hp => ?_⟩
  apply hOV
  exact ⟨hKO hp.1, hball (mem_ball.mpr ((mem_closedBall.mp hp.2).trans_lt (by linarith)))⟩

private theorem exists_cutoffSpray {γ : ℝ → (MetricField dim)} (hγ : ContDiff ℝ ∞ (geodesicSpray γ))
    {K : Set (ℝ × (X dim))} (hK : IsCompact K) :
    ∃ (V : (GeodesicPhase dim) → (GeodesicPhase dim)) (L : ℝ≥0) (U : Set (GeodesicPhase dim)),
      ContDiff ℝ ∞ V ∧ LipschitzWith L V ∧ IsOpen U ∧
      (∀ p ∈ K, (p.1,p.2,0) ∈ U) ∧ EqOn V (geodesicSpray γ) U ∧ ∀ q, (V q).1 = 0 := by
  let C : Set (GeodesicPhase dim) := (fun p : ℝ × (X dim) => (p.1, p.2, (0 : (X dim)))) '' K
  have hC : IsCompact C :=
    hK.image (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  obtain ⟨R, hR, hCR⟩ := hC.isBounded.exists_pos_norm_lt
  let χ : ContDiffBump (0 : (GeodesicPhase dim)) :=
    ⟨R, R + 1, hR, lt_add_one R⟩
  let V : (GeodesicPhase dim) → (GeodesicPhase dim) := fun q => χ q • geodesicSpray γ q
  have hV : ContDiff ℝ ∞ V := χ.contDiff.smul hγ
  have hVc : HasCompactSupport V := χ.hasCompactSupport.smul_right
  obtain ⟨L, hL⟩ := hV.lipschitzWith_of_hasCompactSupport hVc (by simp)
  refine ⟨V, L, ball 0 R, hV, hL, isOpen_ball, ?_, ?_, ?_⟩
  · intro p hp
    exact mem_ball_zero_iff.mpr (hCR _ ⟨p, hp, rfl⟩)
  · intro q hq
    have h := χ.one_of_mem_closedBall (ball_subset_closedBall hq)
    simp only [V, h, one_smul]
  · intro q
    change χ q * 0 = 0
    exact mul_zero _

/-- One signed-time room about the compact family of stationary phases.
The radial identity is the actual time reparametrization of the same flow. -/
structure GeodesicFlowOn (γ : ℝ → (MetricField dim)) (K : Set (ℝ × (X dim)))
    (r : ℝ) (F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim)) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : (GeodesicPhase dim) × ℝ => F p.1 p.2)
  initial : ∀ q, F q 0 = q
  stationary : ∀ p ∈ K, ∀ t, F (p.1,p.2,0) t = (p.1,p.2,0)
  parameter : ∀ q t, (F q t).1 = q.1
  derivative : ∀ p ∈ K, ∀ v ∈ closedBall (0 : (X dim)) r, ∀ t ∈ Icc (-2 : ℝ) 2,
    HasDerivAt (F (p.1,p.2,v)) (geodesicSpray γ (F (p.1,p.2,v) t)) t
  radial : ∀ p ∈ K, ∀ v ∈ closedBall (0 : (X dim)) r, ∀ t ∈ Icc (-2 : ℝ) 2,
    F (p.1,p.2,t • v) 1 = geodesicPhaseScale t (F (p.1,p.2,v) t)

set_option maxHeartbeats 1200000 in
theorem exists_geodesicFlowOn {γ : ℝ → (MetricField dim)} (hγ : ContDiff ℝ ∞ (geodesicSpray γ))
    {K : Set (ℝ × (X dim))} (hK : IsCompact K) :
    ∃ (r : ℝ) (F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim)), 0 < r ∧ GeodesicFlowOn γ K r F := by
  obtain ⟨V, L, U, hV, hL, hU, hKsub, hEq, hVfst⟩ := exists_cutoffSpray hγ hK
  let F := ODE.globalSolution V hL
  have hF := contDiff_infty_globalFlow V hL hV
  have hrest (p : ℝ × (X dim)) (hp : p ∈ K) (t : ℝ) : F (p.1,p.2,0) t = (p.1,p.2,0) :=
    globalFlow_rest V hL ((hEq (hKsub p hp)).trans (geodesicSpray_rest γ _ _)) t
  have hparam (q : (GeodesicPhase dim)) (t : ℝ) : (F q t).1 = q.1 := by
    have hd (s : ℝ) : HasDerivAt (fun u => (F q u).1) 0 s := by
      have hh := (ContinuousLinearMap.fst ℝ ℝ ((X dim) × (X dim))).hasFDerivAt.comp_hasDerivAt s
        (ODE.hasDerivAt_globalSolution V hL q s)
      simpa only [ContinuousLinearMap.coe_fst', Function.comp_def, hVfst] using hh
    have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    simpa only [F, ODE.globalSolution_zero] using hc
  let T := K ×ˢ (Icc (-2 : ℝ) 2 ×ˢ Icc (0 : ℝ) 1)
  let H (q : ((ℝ × (X dim)) × ℝ × ℝ) × (X dim)) : (GeodesicPhase dim) :=
    F (q.1.1.1,q.1.1.2,q.2) (q.1.2.1 * q.1.2.2)
  let H' (q : ((ℝ × (X dim)) × ℝ × ℝ) × (X dim)) : (GeodesicPhase dim) :=
    geodesicPhaseScale q.1.2.1 (H q)
  have hH : Continuous H := by
    have hh : Continuous (fun q : ((ℝ × (X dim)) × ℝ × ℝ) × (X dim) =>
        ((q.1.1.1,q.1.1.2,q.2), q.1.2.1 * q.1.2.2)) := by fun_prop
    exact hF.continuous.comp hh
  have hH' : Continuous H' := by
    simp only [H', geodesicPhaseScale_apply]
    fun_prop
  have hO : IsOpen (H ⁻¹' U ∩ H' ⁻¹' U) := (hU.preimage hH).inter (hU.preimage hH')
  have hzero : T ×ˢ ({0} : Set (X dim)) ⊆ H ⁻¹' U ∩ H' ⁻¹' U := by
    rintro ⟨⟨p, t, s⟩, v⟩ ⟨hp, hv⟩
    have hv' : v = 0 := hv
    subst v
    have hpK : p ∈ K := hp.1
    have hh : H ((p,t,s),0) = (p.1,p.2,0) := hrest p hpK _
    refine ⟨?_, ?_⟩
    · change H ((p,t,s),0) ∈ U
      rw [hh]
      exact hKsub p hpK
    · change geodesicPhaseScale t (H ((p,t,s),0)) ∈ U
      rw [hh, geodesicPhaseScale_apply, smul_zero]
      exact hKsub p hpK
  obtain ⟨r, hr, hroom⟩ := exists_closedBall_of_compact_zeroSlice
    (hK.prod (isCompact_Icc.prod isCompact_Icc)) hO hzero
  have hU₂ (p : ℝ × (X dim)) (hp : p ∈ K) (v : (X dim)) (hv : v ∈ closedBall (0 : (X dim)) r)
      (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      F (p.1,p.2,v) (t*s) ∈ U ∧ geodesicPhaseScale t (F (p.1,p.2,v) (t*s)) ∈ U :=
    hroom (show ((p,t,s),v) ∈ T ×ˢ closedBall (0 : (X dim)) r from ⟨⟨hp, ht, hs⟩, hv⟩)
  refine ⟨r, F, hr, hF, ODE.globalSolution_zero V hL, hrest, hparam, ?_, ?_⟩
  · intro p hp v hv t ht
    have h := (hU₂ p hp v hv t ht 1 (by simp)).1
    rw [mul_one] at h
    simpa only [F, hEq h] using ODE.hasDerivAt_globalSolution V hL (p.1,p.2,v) t
  · intro p hp v hv t ht
    let q₀ : (GeodesicPhase dim) := (p.1,p.2,v)
    let q₁ : (GeodesicPhase dim) := (p.1,p.2,t • v)
    let scaled (s : ℝ) := geodesicPhaseScale t (F q₀ (t*s))
    have hscaled (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) :
        HasDerivAt scaled (V (scaled s)) s := by
      have hroom' := hU₂ p hp v hv t ht s ⟨hs.1, hs.2.le⟩
      have hts : HasDerivAt (fun u : ℝ => t * u) t s := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul t
      have hd := (ODE.hasDerivAt_globalSolution V hL q₀ (t*s)).scomp s hts
      have hlin := (geodesicPhaseScale t).hasFDerivAt.comp_hasDerivAt s hd
      have htH : V (F q₀ (t*s)) = geodesicSpray γ (F q₀ (t*s)) := hEq hroom'.1
      have htS : V (scaled s) = geodesicSpray γ (scaled s) := hEq hroom'.2
      rw [htS, show scaled s = geodesicPhaseScale t (F q₀ (t*s)) from rfl,
        geodesicSpray_reparametrize, ← htH]
      simpa only [scaled, F, Function.comp_def, mul_one, map_smul] using hlin
    have hc : Continuous scaled :=
      (geodesicPhaseScale t).continuous.comp
        ((ODE.continuous_globalSolution_apply V hL q₀).comp (continuous_const.mul continuous_id))
    have h0 : scaled 0 = F q₁ 0 := by
      simp only [scaled, mul_zero, F, ODE.globalSolution_zero, q₀, q₁, geodesicPhaseScale_apply]
    have hu := ODE_solution_unique (v := fun _ => V) (fun _ => hL) hc.continuousOn
      (fun s hs => (hscaled s hs).hasDerivWithinAt)
      (ODE.continuous_globalSolution_apply V hL q₁).continuousOn
      (fun s _ => (ODE.hasDerivAt_globalSolution V hL q₁ s).hasDerivWithinAt) h0
    exact (show scaled 1 = F q₁ 1 from hu (show (1 : ℝ) ∈ Icc 0 1 by norm_num)).symm.trans
      (by simp [scaled, q₀])

end CalderonN
