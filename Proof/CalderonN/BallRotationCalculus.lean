module

public import Proof.CalderonN.SmoothSphereRotation
public import Proof.CalderonN.SmoothBallDivergence

import Proof.CalderonN.ChartBilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic

/-! Linear vector fields on the fixed ball. Plane rotation preserves
the volume pairing, and commutes with the radial derivative. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 21
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {dim : ℕ}

@[expose] def ballRotationGeneratorL (i j : Fin dim) : X dim →L[ℝ] X dim :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (axis j) -
    (EuclideanSpace.proj (𝕜 := ℝ) j).smulRight (axis i)

theorem ballRotationGeneratorL_apply (i j : Fin dim) (x : X dim) :
    ballRotationGeneratorL i j x = rotationVector i j x := by
  unfold ballRotationGeneratorL rotationVector
  simp only [sub_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,axis]

theorem inner_ballRotationGeneratorL_skew (i j : Fin dim) (x y : X dim) :
    ⟪x,ballRotationGeneratorL i j y⟫_ℝ = -⟪ballRotationGeneratorL i j x,y⟫_ℝ := by
  simp only [ballRotationGeneratorL,sub_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,
    inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,axis,
    EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,conj_trivial,one_mul]
  ring

theorem inner_ballRotationGeneratorL_self_eq_zero (i j : Fin dim) (x : X dim) :
    ⟪x,ballRotationGeneratorL i j x⟫_ℝ = 0 := by
  have h := inner_ballRotationGeneratorL_skew i j x x
  rw [real_inner_comm x (ballRotationGeneratorL i j x)] at h
  linarith only [h]

theorem norm_ballRotationGeneratorL_le (i j : Fin dim) : ‖ballRotationGeneratorL i j‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  have hs (k : Fin dim) : ‖axis k‖ = 1 := by rw [axis,PiLp.norm_single]; norm_num
  simp only [ballRotationGeneratorL,sub_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_smul,hs,mul_one]
  change ‖z i‖+‖z j‖ ≤ 2*‖z‖
  linarith only [PiLp.norm_apply_le z i,PiLp.norm_apply_le z j]

theorem diagonal_ballRotationGeneratorL (i j k : Fin dim) : ballRotationGeneratorL i j (axis k) k = 0 := by
  simp only [ballRotationGeneratorL,sub_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,
    PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  classical
  by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [axis,PiLp.single_apply,hi,hj,eq_comm]

/-- Derivative of the directional derivative along a linear vector field. -/
theorem fderiv_linearDirectional_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : X dim →L[ℝ] X dim) {u : X dim → V}
    (hu : ContDiff ℝ ∞ u) (x v : X dim) :
    fderiv ℝ (fun z => fderiv ℝ u z (L z)) x v =
      fderiv ℝ (fderiv ℝ u) x v (L x)+fderiv ℝ u x (L v) := by
  have h := ((hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt.clm_apply
    (L.hasFDerivAt (x := x))
  have he := congrArg (fun T : X dim →L[ℝ] V => T v) h.fderiv
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,add_comm] using he

theorem linearDirectional_commutator (L M : X dim →L[ℝ] X dim) {u : X dim → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : X dim) :
    fderiv ℝ (fun y => fderiv ℝ u y (M y)) x (L x) -
      fderiv ℝ (fun y => fderiv ℝ u y (L y)) x (M x) =
      fderiv ℝ u x (M (L x)-L (M x)) := by
  rw [fderiv_linearDirectional_apply M hu,fderiv_linearDirectional_apply L hu,map_sub]
  have hh := (hu.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) (L x) (M x)
  rw [hh]
  ring

theorem sphereRotationDerivative_comm_radial (i j : Fin dim) {u : X dim → ℝ}
    (hu : ContDiff ℝ ∞ u) (x : X dim) :
    sphereRotationDerivative i j (fun z => fderiv ℝ u z z) x =
      fderiv ℝ (sphereRotationDerivative i j u) x x := by
  have h := linearDirectional_commutator (ballRotationGeneratorL i j) (ContinuousLinearMap.id ℝ (X dim)) hu x
  simp only [ContinuousLinearMap.id_apply,ballRotationGeneratorL_apply,sub_self,map_zero] at h
  exact sub_eq_zero.mp h

variable [NeZero dim] [Nontrivial (Fin dim)]

/-- The solid rotation generator is skew for integration on the ball,
as the corresponding vector field is divergence-free and tangent. -/
theorem integral_ball_sphereRotationDerivative_eq_zero (i j : Fin dim) {u : X dim → ℝ}
    (hu : ContDiff ℝ ∞ u) :
    (∫ z in ball (0 : X dim) 1, sphereRotationDerivative i j u z) = 0 := by
  let J := ballRotationGeneratorL i j
  let W (z : X dim) := u z • J z
  have hW : ContDiff ℝ ∞ W := hu.smul J.contDiff
  have hDiv (z : X dim) : coordinateFluxDivergence W z = sphereRotationDerivative i j u z := by
    have h (k : Fin dim) : coordDeriv k (fun x => W x k) z =
        coordDeriv k u z*(J z) k := by
      have hProj := ((EuclideanSpace.proj (𝕜 := ℝ) k).comp J).hasFDerivAt (x := z)
      change fderiv ℝ (fun x => u x*(J x) k) z (axis k) = _
      have h := congrArg (fun T : X dim →L[ℝ] ℝ => T (axis k))
        ((hu.differentiable (by simp) z).hasFDerivAt.mul hProj).fderiv
      simp only [ContinuousLinearMap.comp_apply,PiLp.proj_apply,add_apply,smul_apply,smul_eq_mul] at h
      rw [diagonal_ballRotationGeneratorL i j k,mul_zero,zero_add] at h
      exact h.trans (by unfold coordDeriv; ring)
    change (∑ k, coordDeriv k (fun x => W x k) z) = _
    simp only [h]
    rw [sphereRotationDerivative,← ballRotationGeneratorL_apply,covector_axis_sum]
    rfl
  rw [← integral_congr_ae (Filter.Eventually.of_forall hDiv),
    integral_unitBall_coordinateFluxDivergence W hW,unitSphereFlux]
  apply integral_eq_zero_of_ae
  filter_upwards with w
  change ⟪(w : X dim),u w • J w⟫_ℝ = 0
  rw [real_inner_smul_right,inner_ballRotationGeneratorL_self_eq_zero,mul_zero]

end CalderonN
