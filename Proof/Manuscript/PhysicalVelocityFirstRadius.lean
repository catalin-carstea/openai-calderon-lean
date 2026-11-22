module

public import Proof.CalderonN.ActualMovingVelocityTaylor

import Proof.CalderonN.NormalizedCenterDerivative
import Proof.CalderonN.NormalEndpointHessian
import Proof.CalderonN.IndexedPolynomialHessian
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The first signed-radius derivative of the scaled pullback velocity is
zero for every fixed slope. The vertical and parallel-center Jacobians
have the same first derivative by the geodesic Hessian and torsion symmetry. -/
theorem scaledNormalTraceVelocity_first_radius_zero
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ : MetricField dim} {K : ℝ} (hγ : Elliptic Ω K γ)
    {E : X dim × X dim → X dim} (hE : ContDiff ℝ ∞ E)
    {R : X dim → ℝ} (hN : NormalCoordinates Y Ω γ E R)
    {e : Frame dim}
    (he : ∀ y ∈ Y, ∀ j k, metricPair γ y (e y j) (e y k) = if j=k then 1 else 0)
    {y : X dim} (hy : y ∈ Y) (b : ℝ) (z a : X dim) :
    HasDerivAt (fun s : ℝ => scaledNormalTraceVelocity γ E e y s b z a) 0 0 := by
  let w := frameVector e y z
  let v (s : ℝ) := s • w
  let H := fderiv ℝ (fderiv ℝ E) (y,0)
  let F (s : ℝ) := fderiv ℝ E (y,v s)
  have hyΩ := hN.center_mem hy
  have hVert (x : X dim) (hx : x ∈ Y) (u : X dim) : fderiv ℝ E (x,0) (0,u) = u :=
    hN.vertical_zero hx e (he x hx) u
  have hEv : ∀ᶠ s in 𝓝 (0 : ℝ), v s ∈ disk γ y (R y) := by
    let D := interior (disk γ y (R y))
    have h0 : (0 : X dim) ∈ D := mem_interior_disk_of_metricPair_lt γ y 0 (R y) (by
      simp only [metricPair,PiLp.zero_apply,mul_zero,Finset.sum_const_zero];
      exact sq_pos_of_pos (hN.2 y hy).1)
    have hv : Continuous v := continuous_id.smul continuous_const
    have he : ∀ᶠ s in 𝓝 (0 : ℝ), v s ∈ D := hv.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds (show v 0 ∈ D by simpa [v] using h0))
    exact he.mono (fun _ hs => interior_subset hs)
  have hD : HasFDerivAt (fderiv ℝ E) H (y,0) :=
    ((hE.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _).hasFDerivAt
  have hBase : HasDerivAt (fun s : ℝ => (y+s • a,(0 : X dim))) (a,0) 0 := by
    simpa [id_def] using (((hasDerivAt_id (0:ℝ)).smul_const a).const_add y).prodMk
      (hasDerivAt_const (0:ℝ) (0 : X dim))
  have hMixA : H (a,0) (0,w) = 0 := by
    let f (s : ℝ) := fderiv ℝ E (y+s • a,0) (0,w)
    have hf : HasDerivAt f (H (a,0) (0,w)) 0 := by
      have h := (hD.comp_hasDerivAt_of_eq 0 hBase (by simp)).clm_apply
        (hasDerivAt_const (0:ℝ) ((0 : X dim),w))
      simpa only [Function.comp_apply,map_zero,add_zero] using h
    have heq : f =ᶠ[𝓝 (0:ℝ)] fun _ => w := by
      have hc : Continuous (fun s : ℝ => y+s • a) := continuous_const.add (continuous_id.smul continuous_const)
      filter_upwards [hc.continuousAt.preimage_mem_nhds (hY.mem_nhds (show y+0 • a ∈ Y by simpa using hy))]
        with s hs
      exact hVert _ hs _
    exact hf.unique ((hasDerivAt_const (0:ℝ) w).congr_of_eventuallyEq heq)
  have hMix : H (0,w) (a,0) = 0 :=
    ((hE.contDiffAt (x := (y,0))).isSymmSndFDerivAt (by simp)).eq (0,w) (a,0) |>.trans hMixA
  have hCurve : HasDerivAt (fun s : ℝ => (y,v s)) (0,w) 0 := by
    simpa [v,id_def] using (hasDerivAt_const (0:ℝ) y).prodMk ((hasDerivAt_id (0:ℝ)).smul_const w)
  have hF : HasDerivAt F (H (0,w)) 0 := by
    exact hD.comp_hasDerivAt_of_eq 0 hCurve (by simp [v])
  let U (s : ℝ) := normalizedParallelCenterJacobian γ E y (v s) a
  let C (s : ℝ) := normalParallelCenterJacobian γ E y (v s) a
  have hEq : (fun s => F s (0,U s)) =ᶠ[𝓝 (0:ℝ)] C := by
    filter_upwards [hEv] with s hs
    have heq := (hN.normalVerticalJacobian_isInvertible hy (v s) hs).self_apply_inverse
      (normalParallelCenterJacobian γ E y (v s) a)
    exact heq
  have hU₀ : U 0 = a := by
    have hh := hEq.eq_of_nhds
    change fderiv ℝ E (y,v 0) (0,U 0) = normalParallelCenterJacobian γ E y (v 0) a at hh
    have hv0 : v 0 = 0 := zero_smul _ _
    rw [hv0,hVert y hy,normalParallelCenterJacobian_apply,← connectionBilinear_apply,map_zero,neg_zero] at hh
    have hId := (hN.hasFDerivAt_zero hY hy e (he y hy)).fderiv
    simpa [hId] using hh
  have hUd : DifferentiableAt ℝ U 0 := by
    have hG := hN.contDiffAt_normalizedParallelCenterJacobian hy (0 : X dim) (zero_mem_disk γ y (R y))
    have hG' : ContDiffAt ℝ ∞ (normalizedParallelCenterJacobian γ E y) (v 0) := by
      simpa [v] using hG
    have hv : ContDiff ℝ ∞ v := contDiff_id.smul contDiff_const
    exact ((hG'.comp 0 hv.contDiffAt).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hFapp : HasDerivAt (fun s => F s (0,U s))
      (-connection γ y w a + deriv U 0) 0 := by
    have hApp := hF.clm_apply ((hasDerivAt_const (0:ℝ) (0:X dim)).prodMk hUd.hasDerivAt)
    simpa only [hU₀,F,v,H,zero_smul,hVert y hy,hN.second_vertical hΩ hγ hy hyΩ w a] using hApp
  have hC : HasDerivAt C (-connection γ y a w) 0 := by
    have hA : HasDerivAt (fun s : ℝ => (a,-s • connection γ y a w))
        (0,-connection γ y a w) 0 := by
      simpa [id_def,neg_smul] using (hasDerivAt_const (0:ℝ) a).prodMk
        (((hasDerivAt_id (0:ℝ)).smul_const (connection γ y a w)).neg)
    have hApp := hF.clm_apply hA
    have heq : C = fun s => F s (a,-s • connection γ y a w) := by
      funext s
      rw [show C s = normalParallelCenterJacobian γ E y (v s) a from rfl,
        normalParallelCenterJacobian_apply]
      change fderiv ℝ E (y,v s) (a,-connection γ y a (s • w)) = _
      rw [← connectionBilinear_apply,map_smul,connectionBilinear_apply,neg_smul]
    rw [heq]
    simpa only [zero_smul,neg_zero,F,v,hMix,hVert y hy,zero_add] using hApp
  have hDer : deriv U 0 = 0 := by
    have h := (hFapp.congr_of_eventuallyEq hEq.symm).unique hC
    rw [connection_symmetric hΩ hγ hyΩ w a] at h
    exact add_left_cancel (h.trans (add_zero (-connection γ y a w)).symm)
  have hOut : HasDerivAt (fun s => frameCoordinatesL γ y (e y) (U s) + b • z) 0 0 := by
    have h0 : HasDerivAt U 0 0 := hDer ▸ hUd.hasDerivAt
    simpa only [Function.comp_apply,map_zero] using
      (((frameCoordinatesL γ y (e y)).hasFDerivAt.comp_hasDerivAt 0 h0).add_const (b • z))
  exact hOut.congr_of_eventuallyEq (hEv.mono fun s hs =>
    scaledNormalTraceVelocity_eq_center_add_radius hN e hy (he y hy) s b z a hs)

end CalderonPaper
