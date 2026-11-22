module

public import Proof.CalderonN.MovingTrace
public import Mathlib.Geometry.Manifold.Instances.Sphere

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

public section

noncomputable section

open Set Metric MeasureTheory CalderonN
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {dim : ℕ} [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]

abbrev StereoRadialSpace (dim : ℕ) := X (dim-1) × ℝ

/-- An arbitrary underlying linear identification for using the
square-coordinate Jacobian theorem. Its Haar factor is kept explicit. -/
def stereoRadialCoordinates (h : 1 ≤ dim) : X dim ≃L[ℝ] StereoRadialSpace dim :=
  (LinearEquiv.ofFinrankEq (R := ℝ) (M := X dim) (M' := StereoRadialSpace dim) (by
    simp [StereoRadialSpace, Module.finrank_prod]
    omega)).toContinuousLinearEquiv

/-- The ambient radial map in the chosen Euclidean coordinates. -/
@[expose] def stereoRadialMap (h : 1 ≤ dim) (v : ↥(standardSphere dim)) (q : StereoRadialSpace dim) :
    StereoRadialSpace dim :=
  stereoRadialCoordinates h (q.2 • ((stereographic' (dim-1) v).symm q.1 : X dim))

theorem stereoRadialMap_apply (h : 1 ≤ dim) (v : ↥(standardSphere dim)) (q : StereoRadialSpace dim) :
    stereoRadialMap h v q =
      stereoRadialCoordinates h (q.2 • ((stereographic' (dim-1) v).symm q.1 : X dim)) := rfl

theorem contDiff_stereoRadialMap (h : 1 ≤ dim) (v : ↥(standardSphere dim)) :
    ContDiff ℝ ∞ (stereoRadialMap h v) := by
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (dim-1)
    (𝕜 := ℝ) (ne_zero_of_mem_unit_sphere v)).repr
  let A := ((ℝ ∙ (v : X dim))ᗮ.subtypeL).comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hU : ContDiff ℝ ∞ (fun z : X (dim-1) => ((stereographic' (dim-1) v).symm z : X dim)) := by
    have hE (x : X (dim-1)) : ((stereographic' (dim-1) v).symm x : X dim) =
        stereoInvFunAux (v : X dim) (A x) := rfl
    simp only [hE]
    exact contDiff_stereoInvFunAux.comp A.contDiff
  exact (stereoRadialCoordinates h).contDiff.comp
    (contDiff_snd.smul (hU.comp contDiff_fst))

theorem stereoRadialMap_injOn (h : 1 ≤ dim) (v : ↥(standardSphere dim)) :
    InjOn (stereoRadialMap h v) ((univ : Set (X (dim-1))) ×ˢ Ioi (0 : ℝ)) := by
  let κ := stereographic' (dim-1) v
  intro p hp q hq he
  have he' := (stereoRadialCoordinates h).injective he
  change p.2 • (κ.symm p.1 : X dim) = q.2 • (κ.symm q.1 : X dim) at he'
  have hp₂ : 0 < p.2 := hp.2
  have hq₂ : 0 < q.2 := hq.2
  have hr : p.2 = q.2 := by
    have hn := congrArg norm he'
    simpa only [norm_smul, Real.norm_of_nonneg hp₂.le, Real.norm_of_nonneg hq₂.le,
      norm_eq_of_mem_sphere (κ.symm p.1), norm_eq_of_mem_sphere (κ.symm q.1), mul_one] using hn
  have hAng : κ.symm p.1 = κ.symm q.1 := by
    apply Subtype.ext
    rw [← hr] at he'
    exact (smul_right_injective (X dim) hp₂.ne') he'
  have hTarget : κ.target = univ := stereographic'_target (n := dim-1) v
  have hp₁ : p.1 ∈ κ.target := hTarget.symm ▸ mem_univ _
  have hq₁ : q.1 ∈ κ.target := hTarget.symm ▸ mem_univ _
  exact Prod.ext (κ.symm.injOn hp₁ hq₁ hAng) hr

/-- Each radial coordinate Jacobian is nondegenerate at positive radii.
A local smooth left inverse normalizes the ambient point and applies the
stereographic map, and also records its Euclidean norm. -/
theorem stereoRadialMap_det_ne_zero (h : 1 ≤ dim) (v : ↥(standardSphere dim))
    (q : StereoRadialSpace dim) (hq : 0 < q.2) :
    (fderiv ℝ (stereoRadialMap h v) q).det ≠ 0 := by
  let e := stereoRadialCoordinates h
  let κ := stereographic' (dim-1) v
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (dim-1)
    (𝕜 := ℝ) (ne_zero_of_mem_unit_sphere v)).repr
  let normalize (x : X dim) := ‖x‖⁻¹ • x
  let decode (x : StereoRadialSpace dim) :=
    (U (stereoToFun (v : X dim) (normalize (e.symm x))), ‖e.symm x‖)
  let F := stereoRadialMap h v
  have hF : ContDiff ℝ ∞ F := contDiff_stereoRadialMap h v
  have hN (p : StereoRadialSpace dim) (hp : 0 < p.2) : normalize (e.symm (F p)) = (κ.symm p.1 : X dim) := by
    have he : e.symm (F p) = p.2 • (κ.symm p.1 : X dim) := e.symm_apply_apply _
    simp [normalize,he,norm_smul,Real.norm_of_nonneg hp.le,norm_eq_of_mem_sphere (κ.symm p.1),
      inv_smul_smul₀ hp.ne']
  have hV (p : StereoRadialSpace dim) (hp : 0 < p.2) : ‖e.symm (F p)‖ = p.2 := by
    have he : e.symm (F p) = p.2 • (κ.symm p.1 : X dim) := e.symm_apply_apply _
    rw [he,norm_smul,Real.norm_of_nonneg hp.le,norm_eq_of_mem_sphere (κ.symm p.1),mul_one]
  have hInv : decode ∘ F =ᶠ[𝓝 q] id := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hq)] with p hp
    have hp' : 0 < p.2 := hp
    have hmem : p.1 ∈ κ.target := (stereographic'_target (n := dim-1) v).symm ▸ mem_univ _
    change (U (stereoToFun (v : X dim) (normalize (e.symm (F p)))), ‖e.symm (F p)‖) = p
    rw [hN p hp',hV p hp']
    exact Prod.ext (κ.right_inv hmem) rfl
  have hQ₀ : e.symm (F q) ≠ 0 := norm_pos_iff.mp (by rw [hV q hq]; exact hq)
  have hNorm : ContDiffAt ℝ ∞ (fun x : StereoRadialSpace dim => ‖e.symm x‖) (F q) :=
    (contDiffAt_norm ℝ hQ₀).comp (F q) e.symm.contDiff.contDiffAt
  have hNormalize : ContDiffAt ℝ ∞ (normalize ∘ e.symm) (F q) :=
    (hNorm.inv (norm_ne_zero_iff.mpr hQ₀)).smul e.symm.contDiff.contDiffAt
  have hPole : (κ.symm q.1 : X dim) ≠ (v : X dim) := by
    have hqMem : q.1 ∈ κ.target := (stereographic'_target (n := dim-1) v).symm ▸ mem_univ _
    have hmem : κ.symm q.1 ∈ κ.source := κ.map_target hqMem
    have hSource : κ.source = {v}ᶜ := stereographic'_source (n := dim-1) v
    rw [hSource] at hmem
    exact fun he => hmem (mem_singleton_iff.mpr (Subtype.ext he))
  have hInner : ⟪(v : X dim), normalize (e.symm (F q))⟫_ℝ ≠ 1 := by
    rw [hN q hq]
    exact (ne_of_lt ((inner_lt_one_iff_real_of_norm_eq_one
      (norm_eq_of_mem_sphere v) (norm_eq_of_mem_sphere (κ.symm q.1))).mpr hPole.symm))
  have hStereo : ContDiffAt ℝ ∞ (stereoToFun (v : X dim)) (normalize (e.symm (F q))) := by
    have hO : IsOpen {x : X dim | innerSL ℝ (v : X dim) x ≠ (1 : ℝ)} :=
      isOpen_compl_singleton.preimage (innerSL ℝ (v : X dim)).continuous
    exact contDiffOn_stereoToFun.contDiffAt (hO.mem_nhds hInner)
  have hDecode : DifferentiableAt ℝ decode (F q) := by
    apply ContDiffAt.differentiableAt _ (n := ∞) (by simp)
    exact (U.contDiff.contDiffAt.comp (F q) (hStereo.comp (F q) hNormalize)).prodMk hNorm
  have hComp := (hDecode.hasFDerivAt.comp q
    (hF.differentiable (by simp) q).hasFDerivAt).fderiv
  rw [hInv.fderiv_eq,fderiv_id] at hComp
  have hLin : LinearMap.id = (fderiv ℝ decode (F q)).toLinearMap.comp
      (fderiv ℝ F q).toLinearMap := congrArg ContinuousLinearMap.toLinearMap hComp
  have hDet := congrArg LinearMap.det hLin
  rw [LinearMap.det_id,LinearMap.det_comp] at hDet
  intro hz
  change LinearMap.det (fderiv ℝ F q).toLinearMap = 0 at hz
  rw [hz,mul_zero] at hDet
  exact one_ne_zero hDet

end CalderonPaper
