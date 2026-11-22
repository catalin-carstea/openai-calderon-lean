module

public import Proof.CalderonN.BallRotationConormal
public import Proof.CalderonN.SmoothStrongBallEstimates
public import Proof.CalderonN.PolynomialConormalFirstVariation

import Proof.CalderonN.PolynomialPoissonFirstVariation
import Mathlib.Tactic

/-! Equations for the angular correction and its explicit flat first
variation, both with zero Dirichlet trace. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem negativeBallDivergence_angularBallCorrection (i j : Fin dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (u v : SmoothData dim)
    (hu : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1))
    (hv : EqOn (negativeBallDivergence a v.1) 0 (ball (0 : X dim) 1)) :
    EqOn (negativeBallDivergence a (angularBallCorrection i j u v).1)
      (-negativeBallDivergence (ballRotationCoefficient i j a) u.1) (ball (0 : X dim) 1) := by
  let w : SmoothData dim := ⟨sphereRotationDerivative i j u.1,
    contDiff_sphereRotationDerivative i j u.1 u.2⟩
  intro z hz
  change negativeBallDivergence a (w.1-v.1) z = -negativeBallDivergence (ballRotationCoefficient i j a) u.1 z
  rw [negativeBallDivergence_sub_solution ha w v,hv hz,Pi.zero_apply,sub_zero]
  have h := sphereRotationDerivative_negativeBallDivergence i j ha u z
  have hG : negativeBallDivergence a u.1 =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hu hx
  rw [sphereRotationDerivative,hG.fderiv_eq,fderiv_fun_const,Pi.zero_apply,zero_apply] at h
  change _ = -negativeBallDivergence (ballRotationCoefficient i j a) u.1 z
  change 0 = negativeBallDivergence a w.1 z+negativeBallDivergence (ballRotationCoefficient i j a) u.1 z at h
  linarith only [h]

theorem negativeBallDivergence_flat_harmonicFiniteDriftVariation
    (ell : X dim →L[ℝ] ℝ) (f : HarmonicFiniteCoefficients dim) (z : X dim) :
    negativeBallDivergence (fun _ => (1 : Mat dim)) (harmonicFiniteDriftVariationSmooth ell f).1 z =
      -negativeBallDivergence (fun x => ell x • (1 : Mat dim)) (harmonicFiniteSmooth f).1 z := by
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth ell f
  have hQ := negativeBallDivergence_scalar (fun _ => (1 : ℝ)) q contDiff_const z
  have hU := negativeBallDivergence_scalar ell u ell.contDiff z
  simp only [one_smul,one_mul,coordDeriv,fderiv_fun_const,Pi.zero_apply,zero_apply,
    zero_mul,Finset.sum_const_zero,add_zero] at hQ
  rw [hQ,hU,harmonicFiniteDriftVariationSmooth_flat_laplace,laplace_flat_harmonicFiniteSmooth]
  simp only [coordDeriv,ContinuousLinearMap.fderiv,mul_zero,zero_add,neg_neg,u]

theorem angularBallCorrection_radialDerivative (i j : Fin dim)
    (u v : SmoothData dim) (z : X dim) :
    fderiv ℝ (angularBallCorrection i j u v).1 z z =
      sphereRotationDerivative i j (fun x => fderiv ℝ u.1 x x) z-fderiv ℝ v.1 z z := by
  change fderiv ℝ (sphereRotationDerivative i j u.1-v.1) z z = _
  rw [fderiv_sub ((contDiff_sphereRotationDerivative i j u.1 u.2).differentiable (by simp) z)
    (v.2.differentiable (by simp) z),sub_apply,sphereRotationDerivative_comm_radial i j u.2 z]

end CalderonN
