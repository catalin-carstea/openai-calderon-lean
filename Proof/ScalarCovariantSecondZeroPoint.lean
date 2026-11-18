import Proof.ScalarCurvatureTriplePointBound
import Proof.BackgroundScalarCurvatureTripleBound
import Proof.ScalarCovariantSecondZeroReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The zero scalar Green remainder uses the SAME shared norm estimate
as the curvature sector, with the genuine negative H1-to-H0 inclusion. -/
theorem scalar_covariant_second_zero_remainder_bound (d : Data) (q : X → ℝ)
    (U : X → SphereSobolev 2) (y a b : X) (μ Q0 Q1 ε β : ℝ)
    (hμ : 0 ≤ μ) (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hβ : 1 ≤ β)
    (hq : |q y| ≤ μ*Q0*ε^2/β^2) (hDq : |fderiv ℝ q y a| ≤ μ*Q1*ε^2/β) :
    |scalarCovariantSecondZeroRemainder d q U a b y| ≤
      (3*Q0+3*Q1)*μ*ε^2*coarseCovariantTripleEnergy d U y β a a b := by
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let u := sphereSobolevInclusionL 2 1 (by norm_num) (U y)
  let Va := I10 (highSectionCovariantDerivative d U y a)
  let Vb := I10 (highSectionCovariantDerivative d U y b)
  have hI : ‖-I10‖ ≤ 1 := by rw [norm_neg];exact norm_sphereSobolevInclusionL_le _ _ _
  have hDq0 : |fderiv ℝ q y a| ≤ μ*Q1*ε^2 := hDq.trans (div_le_self (by positivity) hβ)
  have hZero : |(0:ℝ)| ≤ μ*Q0*ε^2/β^2 := by
    rw [abs_zero]
    positivity
  have hh := scalar_curvature_triple_point_bound_of_value_bound u Va Va Vb (-I10) 0 0
    (fderiv ℝ q y a) (q y) 0 0 μ Q0 Q1 1 ε β hμ hQ0 hQ1 (by norm_num) hβ
    hI (by simp) (by simp) hDq0 hq hZero hZero
  simpa only [scalarCovariantSecondZeroRemainder,coarseCovariantTripleEnergy,I10,u,Va,Vb,
    _root_.neg_apply,_root_.zero_apply,inner_neg_left,inner_zero_left,
    zero_mul,mul_zero,sub_zero,zero_add,add_zero,mul_neg,neg_mul,mul_one,sub_eq_add_neg,neg_zero] using hh

end ShrinkingSpheres
