module

public import Proof.CalderonN.FlatAngularAdjoint

import Proof.CalderonN.EllipticCalculus
import Mathlib.Tactic

/-! Adapted from `FlatVelocityAdjoint` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open OAI.AnisotropicCalderon.SmoothSphereRotation

private theorem laplace_flat_add {t : ℝ} (ht : 0 < t) {u v : (X dim) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : (X dim)) :
    laplace (flatBallMetric t) (fun z => u z + v z) x =
      laplace (flatBallMetric t) u x + laplace (flatBallMetric t) v x := by
  have he (i : (I dim)) : coordDeriv i (fun z => u z + v z) =
      fun z => coordDeriv i u z + coordDeriv i v z :=
    funext (Elliptic.pd_add hu hv)
  have h₂ (i : (I dim)) : coordDeriv i (coordDeriv i (fun z => u z + v z)) x =
      coordDeriv i (coordDeriv i u) x + coordDeriv i (coordDeriv i v) x := by
    rw [he]
    exact Elliptic.pd_add (Elliptic.contDiff_pd hu) (Elliptic.contDiff_pd hv) x
  simp only [laplace_flatBallMetric ht,h₂,Finset.sum_add_distrib,mul_add]

private theorem laplace_flat_const_mul {t : ℝ} (ht : 0 < t) {u : (X dim) → ℝ}
    (hu : ContDiff ℝ ∞ u) (c : ℝ) (x : (X dim)) :
    laplace (flatBallMetric t) (fun z => c*u z) x = c * laplace (flatBallMetric t) u x := by
  have he (i : (I dim)) : coordDeriv i (fun z => c*u z) = fun z => c*coordDeriv i u z :=
    funext (Elliptic.pd_const_mul c hu)
  have h₂ (i : (I dim)) : coordDeriv i (coordDeriv i (fun z => c*u z)) x = c*coordDeriv i (coordDeriv i u) x := by
    rw [he]
    exact Elliptic.pd_const_mul c (Elliptic.contDiff_pd hu) x
  simp only [laplace_flatBallMetric ht,h₂,← Finset.mul_sum]
  ring

private theorem laplace_flat_const {t : ℝ} (ht : 0 < t) (c : ℝ) (x : (X dim)) :
    laplace (flatBallMetric t) (fun _ => c) x = 0 := by
  have he (i : (I dim)) : coordDeriv i (fun _ => c) = fun _ => 0 := by
    funext z
    simp [coordDeriv]
  simp [laplace_flatBallMetric ht,he,coordDeriv]

private theorem conormal_fixedBallPoisson_eq_of_solution
    {g : (MetricField dim)} (hg : SmoothMetric univ g) {d b : (X dim) → ℝ}
    (hb : FixedBallSolution g d b) {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    ballConormal g (fixedBallPoisson g d) w = ballConormal g b w := by
  have h : ∃ u, FixedBallSolution g d u := ⟨b,hb⟩
  have hp : FixedBallSolution g d (fixedBallPoisson g d) := by
    rw [fixedBallPoisson,dite_eq_left h]
    exact Classical.choose_spec h
  have he := eqOn_fixedBallSolution isOpen_univ (subset_univ _) hg hp hb (fun _ _ => rfl)
  rw [ballConormal_eq_fderiv_conormalVector,ballConormal_eq_fderiv_conormalVector,
    eqOn_fderiv_closedUnitBall hp.1 hb.1 he (sphere_subset_closedBall hw)]

/-- The scaled velocity adjoint on constants is exactly the degree-one
term (n a · w), independently of the radial part of the velocity. -/
theorem flatVelocityAdjoint_one {t : ℝ} (ht : 0 < t) (a : (X dim)) (b : ℝ)
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    parametricBallVelocityAdjoint (P := (X dim)) (fun _ => t^2 • (1 : (Mat dim)))
      (fun q => a+b • q.2) (fun _ => 1) (0,w) = (dim : ℝ)*flatLinear a w := by
  let g := flatBallMetric (dim := dim) t
  let V (w : (X dim)) := a+b • w
  let D (w : (X dim)) := (1:ℝ) * conormalComponent g w (V w)
  let B (w : (X dim)) := (t^(dim-2))⁻¹*(flatLinear a w+b)
  have hB : ContDiff ℝ ∞ B := contDiff_const.mul ((contDiff_flatLinear a).add contDiff_const)
  have hSol : FixedBallSolution g D B := by
    refine ⟨hB,fun z hz => ?_,fun z _ => ?_⟩
    · change (t^(dim-2))⁻¹*(flatLinear a z+b) = 1*conormalComponent g z (a+b • z)
      rw [conormalComponent_flat_affineVelocity ht a b hz,one_mul,div_eq_mul_inv,mul_comm]
    · change laplace (flatBallMetric t) (fun z => (t^(dim-2))⁻¹*(flatLinear a z+b)) z = 0
      rw [laplace_flat_const_mul ht ((contDiff_flatLinear a).add (contDiff_const (c := b))),
        laplace_flat_add ht (contDiff_flatLinear a) (contDiff_const (c := b)),
        laplace_flatLinear ht,laplace_flat_const ht,zero_add,mul_zero]
  have hN : ballConormal g (fixedBallPoisson g D) w = flatLinear a w := by
    rw [conormal_fixedBallPoisson_eq_of_solution (smoothMetric_flatBallMetric ht) hSol hw,
      ballConormal_flat ht]
    have h₁ : DifferentiableAt ℝ (fun z => flatLinear a z+b) w :=
      ((contDiff_flatLinear a).differentiable (by simp) w).add_const b
    change t^(dim-2) * fderiv ℝ (fun z => (t^(dim-2))⁻¹*(flatLinear a z+b)) w w = _
    rw [fderiv_const_mul h₁,fderiv_add_const]
    simp only [smul_apply,smul_eq_mul,fderiv_flatLinear_apply,← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ ht.ne'),one_mul]
  rw [parametricBallVelocityAdjoint_on_sphere _ _ _ _ hw]
  change ballVelocityAdjoint g V (fun _ => 1) (fixedBallPoisson g D) w = _
  rw [ballVelocityAdjoint,hN,sum_rotationDerivative_flatVelocity ht a b contDiff_const hw]
  simp [fderiv_const_apply]
  ring

/-- On a linear trace, the translation contributes its trace-free
quadratic component and the radial velocity contributes degree one. -/
theorem flatVelocityAdjoint_linear {t : ℝ} (ht : 0 < t) (a l : (X dim)) (b : ℝ)
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    parametricBallVelocityAdjoint (P := (X dim)) (fun _ => t^2 • (1 : (Mat dim)))
      (fun q => a+b • q.2) (fun q => flatLinear l q.2) (0,w) =
        ((dim : ℝ)+2)*(flatLinear a w*flatLinear l w-flatLinear a l/(dim : ℝ)) + b*flatLinear l w := by
  let g := flatBallMetric (dim := dim) t
  let V (w : (X dim)) := a+b • w
  let D (w : (X dim)) := flatLinear l w * conormalComponent g w (V w)
  let B (w : (X dim)) := (t^(dim-2))⁻¹*(flatHarmonicProduct a l w+b*flatLinear l w)
  have hBL : ContDiff ℝ ∞ (fun w => b*flatLinear l w) := contDiff_const.mul (contDiff_flatLinear l)
  have hBQ : ContDiff ℝ ∞ (fun w => flatHarmonicProduct a l w+b*flatLinear l w) :=
    (contDiff_flatHarmonicProduct a l).add hBL
  have hB : ContDiff ℝ ∞ B := contDiff_const.mul hBQ
  have hSol : FixedBallSolution g D B := by
    refine ⟨hB,fun z hz => ?_,fun z _ => ?_⟩
    · change (t^(dim-2))⁻¹*(flatHarmonicProduct a l z+b*flatLinear l z) =
        flatLinear l z * conormalComponent g z (a+b • z)
      rw [conormalComponent_flat_affineVelocity ht a b hz,flatHarmonicProduct,flatRadiusSq_on_sphere hz]
      ring
    · change laplace (flatBallMetric t) (fun z => (t^(dim-2))⁻¹*(flatHarmonicProduct a l z+b*flatLinear l z)) z = 0
      rw [laplace_flat_const_mul ht hBQ,laplace_flat_add ht (contDiff_flatHarmonicProduct a l) hBL,
        laplace_flatHarmonicProduct ht,laplace_flat_const_mul ht (contDiff_flatLinear l),
        laplace_flatLinear ht,mul_zero,zero_add,mul_zero]
  have hN : ballConormal g (fixedBallPoisson g D) w =
      2*(flatLinear a w*flatLinear l w-flatLinear a l/(dim : ℝ))+b*flatLinear l w := by
    rw [conormal_fixedBallPoisson_eq_of_solution (smoothMetric_flatBallMetric ht) hSol hw,
      ballConormal_flat ht]
    change t^(dim-2) * fderiv ℝ (fun z => (t^(dim-2))⁻¹*(flatHarmonicProduct a l z+b*flatLinear l z)) w w = _
    rw [fderiv_const_mul (hBQ.differentiable (by simp) w),
      fderiv_fun_add ((contDiff_flatHarmonicProduct a l).differentiable (by simp) w)
        (hBL.differentiable (by simp) w),fderiv_const_mul ((contDiff_flatLinear l).differentiable (by simp) w)]
    simp only [smul_apply,smul_eq_mul,_root_.add_apply,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ ht.ne'),one_mul,
      fderiv_flatHarmonicProduct_apply,fderiv_flatLinear_apply]
    rw [show flatLinear w w = 1 from flatRadiusSq_on_sphere hw]
    ring
  rw [parametricBallVelocityAdjoint_on_sphere _ _ _ _ hw]
  change ballVelocityAdjoint g V (flatLinear l) (fixedBallPoisson g D) w = _
  rw [ballVelocityAdjoint,hN,sum_rotationDerivative_flatVelocity ht a b (contDiff_flatLinear l) hw,
    fderiv_flatLinear_apply]
  have he : flatLinear l (a-flatLinear a w • w) =
      flatLinear a l - flatLinear a w * flatLinear l w := by
    simp [flatLinear,inner_sub_right,real_inner_smul_right,real_inner_comm l a]
  rw [he]
  have hd : (dim:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dim)
  field_simp
  ring

end CalderonN
