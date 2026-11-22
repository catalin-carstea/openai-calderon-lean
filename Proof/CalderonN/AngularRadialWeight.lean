module

public import Proof.CalderonN.BallRotationConormal
public import Proof.CalderonN.NormalRadialWeightRemainder

import Proof.CalderonN.ZonalProjection
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! Differentiating the scalar conormal weight along the sphere amounts
to taking the radial row of the rotated coefficient. -/

public section

noncomputable section
open Set
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation OAI.AnisotropicCalderon.SphereHarmonic

variable {dim : ℕ} [NeZero dim]

theorem sphereRotationDerivative_mul (i j : Fin dim) {u v : X dim → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (z : X dim) :
    sphereRotationDerivative i j (fun x => u x*v x) z =
      sphereRotationDerivative i j u z*v z+u z*sphereRotationDerivative i j v z := by
  unfold sphereRotationDerivative
  rw [fderiv_fun_mul (hu.differentiable (by simp) z) (hv.differentiable (by simp) z)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

theorem EqOn.sphereRotationDerivative {u v : X dim → ℝ}
    (h : EqOn u v (standardSphere dim)) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (i j : Fin dim) :
    EqOn (sphereRotationDerivative i j u) (sphereRotationDerivative i j v) (standardSphere dim) := by
  intro z hz
  have he := sphereRotationDerivative_eq_zero_of_sphere_zero i j (u-v) (hu.sub hv)
    (fun w => sub_eq_zero.mpr (h w.property)) ⟨z,hz⟩
  change fderiv ℝ (u-v) z (rotationVector i j z) = 0 at he
  rw [fderiv_sub (hu.differentiable (by simp) z) (hv.differentiable (by simp) z),sub_apply] at he
  exact sub_eq_zero.mp he

theorem sphereRotationDerivative_scalarQuadraticCoefficient (i j : Fin dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) :
    sphereRotationDerivative i j (scalarQuadraticCoefficient a) =
      scalarQuadraticCoefficient (ballRotationCoefficient i j a) := by
  let u : SmoothData dim := ⟨fun z => (1/2 : ℝ)*‖z‖^2,
    contDiff_const.mul (contDiff_norm_sq ℝ)⟩
  have hD (z v : X dim) : fderiv ℝ u.1 z v = ⟪z,v⟫_ℝ := by
    change fderiv ℝ ((1/2 : ℝ) • fun z : X dim => ‖z‖^2) z v = _
    rw [fderiv_const_smul_field]
    simp only [Pi.smul_apply,fderiv_norm_sq_apply,smul_apply,smul_eq_mul,innerSL_apply_apply]
    ring
  have hG (z : X dim) : gradient u.1 z = z := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left,hD]
  have hU (A : X dim → Mat dim) : smoothBallConormal A u.1 = scalarQuadraticCoefficient A := by
    funext z
    rw [smoothBallConormal,smoothBallFlux_eq_gradient,hG,EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial,dotProduct,divergenceMatrixOperatorL_apply_coord,
      scalarQuadraticCoefficient,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have h0 : sphereRotationDerivative i j u.1 = 0 := by
    funext z
    rw [sphereRotationDerivative,← ballRotationGeneratorL_apply,hD,inner_ballRotationGeneratorL_self_eq_zero]
    rfl
  have hFlux0 (z : X dim) : smoothBallFlux a 0 z = 0 := by
    ext k
    simp only [smoothBallFlux_apply,coordDeriv,fderiv_zero,Pi.zero_apply,
      zero_apply,mul_zero,Finset.sum_const_zero,PiLp.zero_apply]
  funext z
  rw [← hU,sphereRotationDerivative_smoothBallConormal i j ha u z,h0,hFlux0,zero_add]
  exact congrFun (hU (ballRotationCoefficient i j a)) z

theorem scalarQuadraticCoefficient_sub (a b : X dim → Mat dim) :
    scalarQuadraticCoefficient (a-b) = scalarQuadraticCoefficient a-scalarQuadraticCoefficient b := by
  funext z
  simp only [scalarQuadraticCoefficient,Pi.sub_apply,Matrix.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem scalarQuadraticCoefficient_smul_linear_at_sphere
    (ell : X dim →L[ℝ] ℝ) (r : ℝ) {z : X dim} (hz : z ∈ standardSphere dim) :
    scalarQuadraticCoefficient (fun w => r • (ell w • (1 : Mat dim))) z = r*ell z := by
  have hN : ∑ i : Fin dim, z i*z i = 1 := by
    have h := unitSphere_sum_sq ⟨z,hz⟩
    simpa only [pow_two] using h
  rw [scalarQuadraticCoefficient]
  have h (k : Fin dim) : (∑ l, z k * (r • ell z • (1 : Mat dim)) k l * z l) =
      (r*ell z)*(z k*z k) := by
    simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,ite_mul,mul_one,mul_zero,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    ring
  simp_rw [h,← Finset.mul_sum,hN,mul_one]

end CalderonN
