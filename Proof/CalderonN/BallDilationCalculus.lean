module

public import Proof.CalderonN.BallRotationFlux
public import Proof.CalderonN.BallRadialDerivative
public import Proof.CalderonN.SmoothStrongBallEstimates

import Mathlib.Tactic

/-! Dilation differentiates the fixed-ball Dirichlet equation in the
relative-radius direction. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Gradient Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def ballDilationCoefficient (a : X dim → Mat dim) : X dim → Mat dim :=
  fun z => fderiv ℝ a z z

theorem contDiff_ballDilationCoefficient {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (ballDilationCoefficient a) :=
  (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_id

private theorem radial_smoothBallFlux (u : SmoothData dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (z : X dim) :
    fderiv ℝ (smoothBallFlux a u.1) z z + smoothBallFlux a u.1 z =
      smoothBallFlux a (fun x => fderiv ℝ u.1 x x) z+
        smoothBallFlux (ballDilationCoefficient a) u.1 z := by
  let L := divergenceMatrixOperatorL dim
  let A := L ∘ a
  have hA : ContDiff ℝ ∞ A := L.contDiff.comp ha
  have hu : ContDiff ℝ ∞ (gradient u.1) := u.2.gradient_right (by simp)
  have hf : smoothBallFlux a u.1 = fun z => A z (gradient u.1 z) :=
    funext (smoothBallFlux_eq_gradient a u.1)
  rw [hf]
  have h := congrArg (fun P : X dim →L[ℝ] X dim => P z)
    ((((hA.differentiable (by simp) z).hasFDerivAt).clm_apply
      (hu.differentiable (by simp) z).hasFDerivAt).fderiv)
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply] at h
  rw [h,fderiv_gradient_along_radial u z,smoothBallFlux_eq_gradient,smoothBallFlux_eq_gradient]
  have h' := (L.hasFDerivAt.comp z (ha.differentiable (by simp) z).hasFDerivAt).fderiv
  change fderiv ℝ A z = _ at h'
  rw [h']
  simp only [map_sub,ContinuousLinearMap.comp_apply,A,Function.comp_apply,L,ballDilationCoefficient]
  abel

/-- For a homogeneous solution the dilation derivative satisfies the
equation with the differentiated coefficient and the original solution. -/
theorem negativeBallDivergence_radial_solution {a : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (u : SmoothData dim)
    (hu : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1)) :
    EqOn (negativeBallDivergence a (fun z => fderiv ℝ u.1 z z))
      (-negativeBallDivergence (ballDilationCoefficient a) u.1) (ball (0 : X dim) 1) := by
  let v := smoothBallRadialDerivative u
  let F := smoothBallFlux a u.1
  let G := smoothBallFlux a v.1
  let H := smoothBallFlux (ballDilationCoefficient a) u.1
  let R (z : X dim) := fderiv ℝ F z z-F z
  have hF := contDiff_smoothBallFlux ha u
  have hR : ContDiff ℝ ∞ R := ((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_id).sub hF
  have hG := contDiff_smoothBallFlux ha v
  have hH := contDiff_smoothBallFlux (contDiff_ballDilationCoefficient ha) u
  have hEq : R+F+F = G+H := by
    funext x
    change fderiv ℝ F x x-F x+F x+F x = G x+H x
    rw [sub_add_cancel]
    exact radial_smoothBallFlux u ha x
  intro z hz
  have hDiv : coordinateFluxDivergence F =ᶠ[𝓝 z] (0 : X dim → ℝ) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx
    rw [coordinateFluxDivergence_smoothBallFlux,hu hx,Pi.zero_apply,neg_zero]
  have h1 := coordinateFluxDivergence_linearDirectional_sub (ContinuousLinearMap.id ℝ (X dim)) hF z
  change coordinateFluxDivergence R z = fderiv ℝ (coordinateFluxDivergence F) z z at h1
  rw [hDiv.fderiv_eq,fderiv_zero,Pi.zero_apply,zero_apply] at h1
  have hd := congrArg (fun A : X dim → X dim => coordinateFluxDivergence A z) hEq
  change coordinateFluxDivergence (R+F+F) z = coordinateFluxDivergence (G+H) z at hd
  have hDF : Differentiable ℝ F := hF.differentiable (by simp)
  have hDR : Differentiable ℝ R := hR.differentiable (by simp)
  have hDG : Differentiable ℝ G := hG.differentiable (by simp)
  have hDH : Differentiable ℝ H := hH.differentiable (by simp)
  rw [coordinateFluxDivergence_add (hDR.add hDF) hDF,
    coordinateFluxDivergence_add hDR hDF,coordinateFluxDivergence_add hDG hDH,
    h1,show coordinateFluxDivergence F z = 0 from hDiv.eq_of_nhds,add_zero,add_zero] at hd
  change 0 = coordinateFluxDivergence (smoothBallFlux a v.1) z+
    coordinateFluxDivergence (smoothBallFlux (ballDilationCoefficient a) u.1) z at hd
  rw [coordinateFluxDivergence_smoothBallFlux,coordinateFluxDivergence_smoothBallFlux] at hd
  change negativeBallDivergence a v.1 z = -negativeBallDivergence (ballDilationCoefficient a) u.1 z
  linarith only [hd]

end CalderonN
