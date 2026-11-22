module

public import Proof.CalderonN.GeodesicFlow

import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ}

/-- Position at time one for the same flow used in the radial path. -/
@[expose] def geodesicEndpoint (F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim))
    (p : (ℝ × (X dim)) × (X dim)) : (X dim) :=
  (F (p.1.1,p.1.2,p.2) 1).2.1

theorem GeodesicFlowOn.contDiff_endpoint {γ : ℝ → (MetricField dim)} {K : Set (ℝ × (X dim))}
    {r : ℝ} {F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim)} (h : GeodesicFlowOn γ K r F) :
    ContDiff ℝ ∞ (geodesicEndpoint F) := by
  have hinput : ContDiff ℝ ∞ (fun p : ((ℝ × (X dim)) × (X dim)) =>
      ((p.1.1,p.1.2,p.2),(1 : ℝ))) := by fun_prop
  exact contDiff_fst.comp (contDiff_snd.comp (h.smooth.comp hinput))

theorem GeodesicFlowOn.endpoint_rest {γ : ℝ → (MetricField dim)} {K : Set (ℝ × (X dim))}
    {r : ℝ} {F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim)} (h : GeodesicFlowOn γ K r F)
    {p : ℝ × (X dim)} (hp : p ∈ K) : geodesicEndpoint F (p,0) = p.2 := by
  exact congrArg (fun z : (GeodesicPhase dim) => z.2.1) (h.stationary p hp 1)

private def phasePosition : (GeodesicPhase dim) →L[ℝ] (X dim) :=
  (ContinuousLinearMap.fst ℝ (X dim) (X dim)).comp (ContinuousLinearMap.snd ℝ ℝ ((X dim) × (X dim)))

private def phaseVelocity : (GeodesicPhase dim) →L[ℝ] (X dim) :=
  (ContinuousLinearMap.snd ℝ (X dim) (X dim)).comp (ContinuousLinearMap.snd ℝ ℝ ((X dim) × (X dim)))

private theorem GeodesicFlowOn.hasDerivAt_radial {γ : ℝ → (MetricField dim)} {K : Set (ℝ × (X dim))}
    {r : ℝ} {F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim)} (h : GeodesicFlowOn γ K r F)
    {p : ℝ × (X dim)} (hp : p ∈ K) {v : (X dim)} (hv : v ∈ closedBall (0 : (X dim)) r)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun s => geodesicEndpoint F (p,s • v)) (F (p.1,p.2,v) t).2.2 t := by
  have he : (fun s => geodesicEndpoint F (p,s • v)) =ᶠ[𝓝 t]
      fun s => (F (p.1,p.2,v) s).2.1 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have he' := congrArg (fun q : (GeodesicPhase dim) => q.2.1) (h.radial p hp v hv s (Ioo_subset_Icc_self hs))
    simpa only [geodesicEndpoint, geodesicPhaseScale_apply] using he'
  have hderiv := phasePosition.hasFDerivAt.comp_hasDerivAt t
    (h.derivative p hp v hv t (Ioo_subset_Icc_self ht))
  have hd : HasDerivAt (fun s => (F (p.1,p.2,v) s).2.1) (F (p.1,p.2,v) t).2.2 t := hderiv
  exact hd.congr_of_eventuallyEq he

theorem GeodesicFlowOn.radial_geodesic {γ : ℝ → (MetricField dim)} {K : Set (ℝ × (X dim))}
    {r : ℝ} {F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim)} (h : GeodesicFlowOn γ K r F)
    {p : ℝ × (X dim)} (hp : p ∈ K) {v : (X dim)} (hv : v ∈ closedBall (0 : (X dim)) r) :
    let path := fun t => geodesicEndpoint F (p,t • v)
    path 0 = p.2 ∧ deriv path 0 = v ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (deriv path) t = -connection (γ p.1) (path t) (deriv path t) (deriv path t) := by
  let path := fun t : ℝ => geodesicEndpoint F (p,t • v)
  let velocity := fun t => (F (p.1,p.2,v) t).2.2
  have hvd (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) : deriv path t = velocity t :=
    (h.hasDerivAt_radial hp hv ht).deriv
  refine ⟨by simpa [path] using h.endpoint_rest hp, ?_, ?_⟩
  · show deriv path 0 = v
    rw [hvd 0 (by norm_num [mem_Ioo]), show velocity 0 = v from
      congrArg (fun q : (GeodesicPhase dim) => q.2.2) (h.initial (p.1,p.2,v))]
  · intro t ht
    have ht' : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have he : deriv path =ᶠ[𝓝 t] velocity :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht') hvd
    have hp' : path t = (F (p.1,p.2,v) t).2.1 := by
      have hh := congrArg (fun q : (GeodesicPhase dim) => q.2.1) (h.radial p hp v hv t (Ioo_subset_Icc_self ht'))
      simpa only [path, geodesicEndpoint, geodesicPhaseScale_apply] using hh
    have ha := phaseVelocity.hasFDerivAt.comp_hasDerivAt t
      (h.derivative p hp v hv t (Ioo_subset_Icc_self ht'))
    have hγ' : (F (p.1,p.2,v) t).1 = p.1 := h.parameter (p.1,p.2,v) t
    have hacc : deriv velocity t = -connection (γ p.1) (path t) (velocity t) (velocity t) := by
      have ha' : deriv velocity t =
          -connection (γ (F (p.1,p.2,v) t).1) (F (p.1,p.2,v) t).2.1 (velocity t) (velocity t) :=
        ha.deriv
      rwa [hγ', ← hp'] at ha'
    change deriv (deriv path) t = _
    rw [he.deriv_eq, hvd t ht', hacc]

theorem GeodesicFlowOn.endpoint_fderiv_at_rest {γ : ℝ → (MetricField dim)} {K : Set (ℝ × (X dim))}
    {r : ℝ} {F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim)} (h : GeodesicFlowOn γ K r F)
    (hr : 0 < r) {p : ℝ × (X dim)} (hp : p ∈ K) :
    fderiv ℝ (fun v => geodesicEndpoint F (p,v)) 0 = ContinuousLinearMap.id ℝ (X dim) := by
  let e := fun v : (X dim) => geodesicEndpoint F (p,v)
  have hE : ContDiff ℝ ∞ e := h.contDiff_endpoint.comp (contDiff_const.prodMk contDiff_id)
  have hD : DifferentiableAt ℝ e 0 := hE.differentiable (by simp) 0
  apply ContinuousLinearMap.ext
  intro w
  let c := r / (‖w‖ + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  let v := c • w
  have hv : v ∈ closedBall (0 : (X dim)) r := by
    apply mem_closedBall_zero_iff.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    change (r / (‖w‖ + 1)) * ‖w‖ ≤ r
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < ‖w‖ + 1)]
    nlinarith
  have hpath := h.hasDerivAt_radial hp hv (t := 0) (by norm_num [mem_Ioo])
  have hv₀ : (F (p.1,p.2,v) 0).2.2 = v :=
    congrArg (fun q : (GeodesicPhase dim) => q.2.2) (h.initial (p.1,p.2,v))
  have hv_lin : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hD' : HasFDerivAt e (fderiv ℝ e 0) ((0 : ℝ) • v) := by simpa only [zero_smul] using hD.hasFDerivAt
  have he := hD'.comp_hasDerivAt 0 hv_lin
  have heq : fderiv ℝ e 0 v = v := (he.unique hpath).trans hv₀
  change fderiv ℝ e 0 w = w
  rw [show fderiv ℝ e 0 v = c • fderiv ℝ e 0 w from map_smul _ _ _] at heq
  exact smul_right_injective (X dim) hc.ne' heq

theorem GeodesicFlowOn.contDiff_endpoint_fderiv {γ : ℝ → (MetricField dim)} {K : Set (ℝ × (X dim))}
    {r : ℝ} {F : (GeodesicPhase dim) → ℝ → (GeodesicPhase dim)} (h : GeodesicFlowOn γ K r F) :
    ContDiff ℝ ∞ (fun p : (ℝ × (X dim)) × (X dim) =>
      fderiv ℝ (fun v => geodesicEndpoint F (p.1,v)) p.2) := by
  let T : (((ℝ × (X dim)) × (X dim)) →L[ℝ] (X dim)) →L[ℝ] ((X dim) →L[ℝ] (X dim)) :=
    (ContinuousLinearMap.compL ℝ (X dim) ((ℝ × (X dim)) × (X dim)) (X dim)).flip
      (ContinuousLinearMap.inr ℝ (ℝ × (X dim)) (X dim))
  have hE := h.contDiff_endpoint
  have hEq (p : (ℝ × (X dim)) × (X dim)) :
      fderiv ℝ (fun v => geodesicEndpoint F (p.1,v)) p.2 = T (fderiv ℝ (geodesicEndpoint F) p) := by
    have hs := (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2)
    exact ((hE.differentiable (by simp) p).hasFDerivAt.comp p.2 hs).fderiv
  simp_rw [hEq]
  exact T.contDiff.comp (hE.fderiv_right (by simp))

end CalderonN
