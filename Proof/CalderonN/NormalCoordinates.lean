module

public import Proof.CalderonN.GeodesicEndpoint
public import Proof.CalderonN.MovingTrace

import Proof.CalderonN.MetricPair
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ}

private theorem bijective_of_norm_sub_id_le_half (A : (X dim) →L[ℝ] (X dim))
    (hA : ‖A - ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2 : ℝ)) : Function.Bijective A := by
  have hi : Function.Injective A := by
    intro x y he
    have hz : A (x-y) = 0 := by rw [map_sub, he, sub_self]
    have hb := ((A - ContinuousLinearMap.id ℝ (X dim)).le_opNorm (x-y)).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg (x-y)))
    simp only [sub_apply, ContinuousLinearMap.id_apply, hz, zero_sub, norm_neg] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (by linarith [norm_nonneg (x-y)] : ‖x-y‖ = 0))
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hi⟩

private theorem injectiveOn_of_near_id {a : ℝ} {f : (X dim) → (X dim)} (hf : ContDiff ℝ ∞ f)
    (h : ∀ v ∈ closedBall (0 : (X dim)) a, ‖fderiv ℝ f v - ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2 : ℝ)) :
    InjOn f (closedBall 0 a) := by
  intro v hv w hw he
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ)
    (f := f) (f' := fderiv ℝ f) (φ := ContinuousLinearMap.id ℝ (X dim)) (C := (1/2 : ℝ))
    (fun z _ => (hf.differentiable (by simp) z).hasFDerivAt.hasFDerivWithinAt) h
    (convex_closedBall 0 a) hv hw
  simp only [he, sub_self, ContinuousLinearMap.id_apply, zero_sub, norm_neg] at hm
  exact (sub_eq_zero.mp (norm_eq_zero.mp (by linarith [norm_nonneg (w-v)] : ‖w-v‖ = 0))).symm

set_option maxHeartbeats 1500000 in
/-- A compact family of reference metrics and centers has a common
positive radius for the protected geodesic normal-coordinate data. -/
theorem exists_uniform_normalCoordinates
    {γ : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hpos : ∀ lam y, (γ lam y).PosDef)
    {Y Ω : Set (X dim)} (hY : IsCompact Y) (hΩ : IsOpen Ω) (hYΩ : Y ⊆ Ω)
    {S : Set ℝ} (hS : IsCompact S) :
    ∃ (ρ : ℝ) (expMap : ℝ → (X dim) × (X dim) → (X dim)), 0 < ρ ∧
      ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => expMap q.1 q.2) ∧
      (∀ lam ∈ S, NormalCoordinates Y Ω (γ lam) (expMap lam) (fun _ => ρ)) := by
  let K : Set (ℝ × (X dim)) := S ×ˢ Y
  have hK : IsCompact K := hS.prod hY
  obtain ⟨r, F, hr, hF⟩ := exists_geodesicFlowOn (contDiff_geodesicSpray hγ hpos) hK
  let E := geodesicEndpoint F
  let J (q : (ℝ × (X dim)) × (X dim)) := fderiv ℝ (fun v => E (q.1,v)) q.2
  have hE : ContDiff ℝ ∞ E := hF.contDiff_endpoint
  have hJ : ContDiff ℝ ∞ J := hF.contDiff_endpoint_fderiv
  let U : Set ((ℝ × (X dim)) × (X dim)) := E ⁻¹' Ω ∩
    {q | ‖J q - ContinuousLinearMap.id ℝ (X dim)‖ < (1/2 : ℝ)}
  have hU : IsOpen U := (hΩ.preimage hE.continuous).inter
    (isOpen_lt (hJ.continuous.sub continuous_const).norm continuous_const)
  have hzero : K ×ˢ ({0} : Set (X dim)) ⊆ U := by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    have he : v = 0 := hv
    subst v
    change E (p,0) ∈ Ω ∧ ‖J (p,0) - ContinuousLinearMap.id ℝ (X dim)‖ < (1/2 : ℝ)
    refine ⟨?_, ?_⟩
    · rw [show E (p,0) = p.2 from hF.endpoint_rest hp]
      exact hYΩ hp.2
    · rw [show J (p,0) = ContinuousLinearMap.id ℝ (X dim) from hF.endpoint_fderiv_at_rest hr hp,
        sub_self, norm_zero]
      norm_num
  obtain ⟨a, ha, hroom⟩ := exists_closedBall_of_compact_zeroSlice hK hU hzero
  let b := min r a
  have hb : 0 < b := lt_min hr ha
  obtain ⟨c, _, hc, _, hmetric⟩ := exists_uniform_metric_comparison hK
    (g := fun q : ℝ × (X dim) => γ q.1 q.2) (fun i j => (hγ i j).continuous.continuousOn)
    (fun q _ => hpos q.1 q.2)
  let ρ := Real.sqrt c * b
  have hρ : 0 < ρ := mul_pos (Real.sqrt_pos.mpr hc) hb
  let expMap : ℝ → (X dim) × (X dim) → (X dim) := fun lam q => E ((lam,q.1),q.2)
  have hExp : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => expMap q.1 q.2) :=
    hE.comp (by fun_prop)
  refine ⟨ρ, expMap, hρ, hExp, fun lam hlam => ?_⟩
  have hExpLam : ContDiff ℝ ∞ (expMap lam) := hExp.comp (contDiff_const.prodMk contDiff_id)
  have hdisk (y : (X dim)) (hy : y ∈ Y) (v : (X dim)) (hv : v ∈ disk (γ lam) y ρ) :
      v ∈ closedBall (0 : (X dim)) b := by
    have hlow : c * ‖v‖ ^ 2 ≤ metricPair (γ lam) y v v := (hmetric (lam,y) ⟨hlam,hy⟩ v).1
    have hs : c * ‖v‖ ^ 2 ≤ ρ ^ 2 := hlow.trans hv
    apply mem_closedBall_zero_iff.mpr
    apply (pow_le_pow_iff_left₀ (norm_nonneg v) hb.le two_ne_zero).mp
    apply le_of_mul_le_mul_left _ hc
    calc
      _ ≤ ρ ^ 2 := hs
      _ = _ := by rw [show ρ = Real.sqrt c * b from rfl, mul_pow, Real.sq_sqrt hc.le]
  refine ⟨⟨univ,isOpen_univ,subset_univ _,hExpLam.contDiffOn⟩, fun y hy => ?_⟩
  let p : ℝ × (X dim) := (lam,y)
  have hp : p ∈ K := ⟨hlam, hy⟩
  have hcol (v : (X dim)) (hv : v ∈ closedBall (0 : (X dim)) a) :
      expMap lam (y,v) ∈ Ω ∧ ‖J (p,v) - ContinuousLinearMap.id ℝ (X dim)‖ < (1/2 : ℝ) :=
    hroom ⟨hp, hv⟩
  have hvalid (v : (X dim)) (hv : v ∈ disk (γ lam) y ρ) : v ∈ closedBall (0 : (X dim)) a :=
    closedBall_subset_closedBall (min_le_right _ _) (hdisk y hy v hv)
  have hInj : InjOn (fun v => expMap lam (y,v)) (closedBall (0 : (X dim)) a) :=
    injectiveOn_of_near_id (hExpLam.comp (contDiff_const.prodMk contDiff_id))
      (fun v hv => (hcol v hv).2.le)
  refine ⟨hρ, hInj.mono hvalid, fun v hv => ⟨(hcol v (hvalid v hv)).1, ?_, ?_⟩⟩
  · exact bijective_of_norm_sub_id_le_half (J (p,v)) (hcol v (hvalid v hv)).2.le
  · exact hF.radial_geodesic hp (closedBall_subset_closedBall (min_le_left _ _) (hdisk y hy v hv))

end CalderonN
