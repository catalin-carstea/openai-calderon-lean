module

public import Proof.CalderonN.ConstantMetricScale
public import Proof.CalderonN.ConormalDecomposition

import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.LinearMetric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! Adapted from `FlatBallPolynomials` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Metric Matrix
open scoped ContDiff InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def flatBallMetric (t : ℝ) : (MetricField dim) := t^2 • (fun _ : (X dim) => (1 : (Mat dim)))

@[expose] def flatLinear (a w : (X dim)) : ℝ := ⟪a,w⟫_ℝ

@[expose] def flatRadiusSq (w : (X dim)) : ℝ := ⟪w,w⟫_ℝ

/-- The degree-two harmonic extension of the product of two linear traces. -/
@[expose] def flatHarmonicProduct (a b w : (X dim)) : ℝ :=
  flatLinear a w * flatLinear b w - (flatLinear a b / (dim : ℝ)) * (flatRadiusSq w - 1)

theorem flatLinear_eq_sum (a w : (X dim)) : flatLinear a w = ∑ i, a i * w i := by
  rw [flatLinear,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem flatRadiusSq_on_sphere {w : (X dim)} (hw : w ∈ (standardSphere dim)) : flatRadiusSq w = 1 := by
  rw [flatRadiusSq,real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp hw,one_pow]

theorem contDiff_flatLinear (a : (X dim)) : ContDiff ℝ ∞ (flatLinear a) := (innerSL ℝ a).contDiff

theorem contDiff_flatRadiusSq : ContDiff ℝ ∞ (flatRadiusSq (dim := dim)) := contDiff_id.inner ℝ contDiff_id

theorem contDiff_flatHarmonicProduct (a b : (X dim)) : ContDiff ℝ ∞ (flatHarmonicProduct a b) :=
  ((contDiff_flatLinear a).mul (contDiff_flatLinear b)).sub
    (contDiff_const.mul (contDiff_flatRadiusSq.sub contDiff_const))

theorem fderiv_flatLinear_apply (a w v : (X dim)) :
    fderiv ℝ (flatLinear a) w v = flatLinear a v := by
  change fderiv ℝ (innerSL ℝ a : (X dim) →L[ℝ] ℝ) w v = _
  rw [ContinuousLinearMap.fderiv]
  rfl

theorem fderiv_flatRadiusSq_apply (w v : (X dim)) :
    fderiv ℝ flatRadiusSq w v = 2 * flatLinear w v := by
  have h := ((hasFDerivAt_id w).inner ℝ (hasFDerivAt_id w)).fderiv
  simp only [id_eq] at h
  change fderiv ℝ (fun z : (X dim) => ⟪z,z⟫_ℝ) w v = _
  rw [h]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    fderivInnerCLM_apply,flatLinear]
  rw [real_inner_comm v w]
  ring

private theorem flatLinear_axis (a : (X dim)) (i : (I dim)) : flatLinear a (axis i) = a i := by
  simp [flatLinear,axis,EuclideanSpace.inner_single_right]

theorem coordDeriv_flatLinear (a : (X dim)) (i : (I dim)) : coordDeriv i (flatLinear a) = fun _ => a i := by
  funext w
  rw [coordDeriv,fderiv_flatLinear_apply,flatLinear_axis]

theorem coordDeriv_flatRadiusSq (i : (I dim)) :
    coordDeriv i flatRadiusSq = fun w => 2 * w i := by
  funext w
  rw [coordDeriv,fderiv_flatRadiusSq_apply,flatLinear_axis]

theorem fderiv_flatHarmonicProduct_apply (a b w v : (X dim)) :
    fderiv ℝ (flatHarmonicProduct a b) w v =
      flatLinear a w*flatLinear b v + flatLinear b w*flatLinear a v -
        (flatLinear a b/(dim : ℝ))*(2*flatLinear w v) := by
  have ha := (contDiff_flatLinear a).differentiable (by simp) w
  have hb := (contDiff_flatLinear b).differentiable (by simp) w
  have hn := (contDiff_flatRadiusSq.sub (contDiff_const (c := (1:ℝ)))).differentiable (by simp) w
  have hAB : DifferentiableAt ℝ (fun z => flatLinear a z * flatLinear b z) w := ha.mul hb
  have hN : DifferentiableAt ℝ (fun z => (flatLinear a b/(dim : ℝ))*(flatRadiusSq z-1)) w := hn.const_mul _
  unfold flatHarmonicProduct
  rw [fderiv_fun_sub hAB hN,fderiv_fun_mul ha hb,fderiv_const_mul hn,
    fderiv_fun_sub (contDiff_flatRadiusSq.differentiable (by simp) w) (differentiableAt_const (1:ℝ))]
  simp only [_root_.sub_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,fderiv_const_apply,sub_zero,
    fderiv_flatLinear_apply,fderiv_flatRadiusSq_apply]

theorem coordDeriv_flatHarmonicProduct (a b : (X dim)) (i : (I dim)) :
    coordDeriv i (flatHarmonicProduct a b) =
      fun w => flatLinear a w*b i + flatLinear b w*a i - flatLinear a b/(dim : ℝ)*(2*w i) := by
  funext w
  rw [coordDeriv,fderiv_flatHarmonicProduct_apply,flatLinear_axis,flatLinear_axis,flatLinear_axis]

theorem smoothMetric_flatBallMetric {t : ℝ} (ht : 0 < t) : SmoothMetric univ (flatBallMetric (dim := dim) t) := by
  refine ⟨fun _ _ => contDiffOn_const,fun _ _ => ?_⟩
  exact Matrix.PosDef.one.smul (sq_pos_of_pos ht)

theorem laplace_flatBallMetric {t : ℝ} (ht : 0 < t) (f : (X dim) → ℝ) (x : (X dim)) :
    laplace (flatBallMetric (dim := dim) t) f x = (t^2)⁻¹ * ∑ i, coordDeriv i (coordDeriv i f) x := by
  have hdet : ((1 : (Mat dim))).det ≠ 0 := by simp
  rw [flatBallMetric,laplace_const_smul (g := fun _ => (1 : (Mat dim))) (x := x) (c := t^2)
    (pow_ne_zero _ ht.ne') hdet (fun _ _ => differentiableAt_const _) f]
  congr 1
  have hΓ (k i j : (I dim)) : christoffel (fun _ => (1 : (Mat dim))) x k i j = 0 := by
    simp [christoffel,coordDeriv]
  simp [laplace,hΓ,Matrix.one_apply,ite_mul]

theorem laplace_flatLinear {t : ℝ} (ht : 0 < t) (a x : (X dim)) :
    laplace (flatBallMetric t) (flatLinear a) x = 0 := by
  simp [laplace_flatBallMetric ht,coordDeriv_flatLinear,coordDeriv]

theorem laplace_flatHarmonicProduct {t : ℝ} (ht : 0 < t) (a b x : (X dim)) :
    laplace (flatBallMetric t) (flatHarmonicProduct a b) x = 0 := by
  have hD (i : (I dim)) : coordDeriv i (coordDeriv i (flatHarmonicProduct a b)) x =
      2*(a i*b i) - (flatLinear a b/(dim : ℝ))*2 := by
    have ha := (contDiff_flatLinear a).differentiable (by simp) x
    have hb := (contDiff_flatLinear b).differentiable (by simp) x
    let Pi := (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ)
    have hPi : DifferentiableAt ℝ (fun z : (X dim) => z i) x := Pi.differentiableAt
    have h₁ : DifferentiableAt ℝ (fun z => flatLinear a z * b i + flatLinear b z * a i) x :=
      (ha.mul_const _).add (hb.mul_const _)
    have h₂ : DifferentiableAt ℝ (fun z : (X dim) => flatLinear a b/(dim : ℝ)*(2*z i)) x :=
      (hPi.const_mul _).const_mul _
    rw [coordDeriv_flatHarmonicProduct,coordDeriv,fderiv_fun_sub h₁ h₂,
      fderiv_fun_add (ha.mul_const _) (hb.mul_const _),fderiv_mul_const ha,fderiv_mul_const hb,
      fderiv_const_mul (hPi.const_mul 2),fderiv_const_mul hPi]
    simp only [_root_.sub_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,
      fderiv_flatLinear_apply,flatLinear_axis]
    change b i*a i + a i*b i - flatLinear a b/(dim : ℝ)*(2*(fderiv ℝ Pi x) (axis i)) = _
    rw [ContinuousLinearMap.fderiv]
    have he : Pi (axis i) = 1 := by simp [Pi,axis]
    rw [he]
    ring
  rw [laplace_flatBallMetric ht]
  simp only [hD,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,flatLinear_eq_sum]
  have hd : (dim:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne dim)
  field_simp
  ring

theorem ballConormalVector_flat {t : ℝ} (ht : 0 < t) (w : (X dim)) :
    ballConormalVector (flatBallMetric t) w = t^(dim-2) • w := by
  have h (i j : (I dim)) : divergenceCoeff (flatBallMetric t) w i j = t^(dim-2) * (1 : (Mat dim)) i j := by
    have hn := Fin.nontrivial_iff_two_le.mp (inferInstance : Nontrivial (Fin dim))
    change divergenceCoeff (fun _ : X dim => t^2 • (1 : Mat dim)) w i j = _
    rw [divergenceCoeff_scale_sq hn (fun _ => (1 : (Mat dim))) t ht w (by simp)]
    simp [divergenceCoeff,chartVolume]
  ext j
  simp only [ballConormalVector,PiLp.toLp_apply,PiLp.smul_apply,smul_eq_mul,h,Matrix.one_apply]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true,mul_one,mul_comm]
  · intro i _ hij
    simp [hij]
  · simp

theorem ballConormal_flat {t : ℝ} (ht : 0 < t) (f : (X dim) → ℝ) (w : (X dim)) :
    ballConormal (flatBallMetric t) f w = t^(dim-2) * fderiv ℝ f w w := by
  rw [ballConormal_eq_fderiv_conormalVector,ballConormalVector_flat ht,map_smul,smul_eq_mul]

end CalderonN
