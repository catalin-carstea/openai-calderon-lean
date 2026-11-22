module

public import Proof.CalderonN.StrictMetricWeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Proof.CalderonN.StrictMetricHessian

import Proof.CalderonN.ProductPhaseAlgebra
import Proof.CalderonN.ChartBilinear
import Proof.CalderonN.MetricPair
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim]

/-- The inverse-distance Carleman phase for a separated annulus. -/
@[expose] def radialWeight (c x : (X dim)) : ℝ := (‖x-c‖^2 : ℝ) ^ (-(1/2):ℝ)

theorem radialWeight_eq_inv_norm (c x : (X dim)) : radialWeight c x = ‖x-c‖⁻¹ := by
  rw [radialWeight,← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg (x-c))]
  norm_num [Real.rpow_neg (norm_nonneg (x-c))]

private def radialSquared (c x : (X dim)) : ℝ := ‖x-c‖^2

private theorem hasFDerivAt_radialSquared (c x : (X dim)) :
    HasFDerivAt (radialSquared c) ((2:ℝ) • innerSL ℝ (x-c)) x := by
  have h : HasFDerivAt (fun z : (X dim) => z-c) (ContinuousLinearMap.id ℝ (X dim)) x :=
    (hasFDerivAt_id x).sub_const c
  have h' := h.norm_sq
  refine h'.congr_fderiv ?_
  ext u
  simp [two_smul]


theorem radialWeight_fderiv {c x : (X dim)} (hx : x ≠ c) (u : (X dim)) :
    fderiv ℝ (radialWeight c) x u =
      -(‖x-c‖^2 : ℝ) ^ (-(3/2):ℝ) * ⟪x-c,u⟫_ℝ := by
  have hq := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) 2
  have h := ((hasFDerivAt_radialSquared c x).rpow_const (p := -(1/2:ℝ)) (Or.inl hq.ne')).fderiv
  change fderiv ℝ (fun y => radialSquared c y ^ (-(1/2:ℝ))) x u = _
  rw [h]
  simp only [_root_.smul_apply, smul_eq_mul, innerSL_apply_apply, radialSquared,inner_sub_left]
  norm_num
  ring

theorem contDiffAt_radialWeight {c x : (X dim)} (hx : x ≠ c) :
    ContDiffAt ℝ ∞ (radialWeight c) x := by
  have h : ContDiff ℝ ∞ (radialSquared c) := (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  exact h.contDiffAt.rpow_const_of_ne (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) 2).ne'

theorem radialWeight_second {c x : (X dim)} (hx : x ≠ c) :
    ∃ D : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ, HasFDerivAt (fderiv ℝ (radialWeight c)) D x ∧
      ∀ u v : (X dim), D u v = 3 * (‖x-c‖^2 : ℝ) ^ (-(5/2):ℝ) * ⟪x-c,u⟫_ℝ * ⟪x-c,v⟫_ℝ -
        (‖x-c‖^2 : ℝ) ^ (-(3/2):ℝ) * ⟪u,v⟫_ℝ := by
  let k (y : (X dim)) := -(radialSquared c y) ^ (-(3/2):ℝ)
  let A (y : (X dim)) := innerSL ℝ (y-c)
  have hq : 0 < radialSquared c x := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) 2
  have hk := ((hasFDerivAt_radialSquared c x).rpow_const (p := -(3/2:ℝ)) (Or.inl hq.ne')).neg
  have hA : HasFDerivAt A (innerSL ℝ) x := by
    simpa only [A,Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using
      (innerSL ℝ : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)
  have hEv : fderiv ℝ (radialWeight c) =ᶠ[𝓝 x] fun y => k y • A y := by
    have hn : ∀ᶠ y in 𝓝 x, y ≠ c := eventually_ne_nhds hx
    filter_upwards [hn] with y hy
    ext u
    exact radialWeight_fderiv hy u
  refine ⟨_,(hk.smul hA).congr_of_eventuallyEq hEv,?_⟩
  intro u v
  have hi (a b : (X dim)) : (innerSL ℝ : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ) a b = ⟪a,b⟫_ℝ := rfl
  simp only [A,radialSquared,_root_.smul_apply,smul_eq_mul,hi,inner_sub_left,_root_.add_apply]
  norm_num
  ring

private theorem identity_metricHessianEval {φ : (X dim) → ℝ} {x : (X dim)}
    {D : (X dim) →L[ℝ] (X dim) →L[ℝ] ℝ} (hD : HasFDerivAt (fderiv ℝ φ) D x) (u v : (X dim)) :
    metricHessianEval (fun _ => (1 : (Mat dim))) φ x u v = D u v := by
  have hsecond (i j : (I dim)) : coordDeriv i (coordDeriv j φ) x = D (axis i) (axis j) := by
    let L := ContinuousLinearMap.apply ℝ ℝ (axis j)
    have h := L.hasFDerivAt.comp x hD
    change fderiv ℝ (L ∘ fderiv ℝ φ) x (axis i) = _
    rw [h.fderiv]
    rfl
  have hconn (k i j : (I dim)) : christoffel (fun _ => (1 : (Mat dim))) x k i j = 0 := by
    simp [christoffel,coordDeriv]
  simp only [metricHessianEval,metricHessian,hessian,hconn,zero_mul,Finset.sum_const_zero,
    sub_zero,hsecond]
  let L := (ContinuousLinearMap.apply ℝ ℝ v).comp D
  have hL : L u = D u v := rfl
  rw [← hL,covector_axis_sum L u]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (D (axis i) v) * u i
  rw [covector_axis_sum (D (axis i)) v,dotProduct,Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem radialWeight_gradient {c x : (X dim)} (hx : x ≠ c) :
    chartMetricGradient (fun _ => (1 : (Mat dim))) (radialWeight c) x =
      (-(‖x-c‖^2 : ℝ) ^ (-(3/2):ℝ)) • (x-c) := by
  ext i
  change (((1 : (Mat dim))⁻¹) *ᵥ (fun i => coordDeriv i (radialWeight c) x)) i = _
  rw [inv_one,Matrix.one_mulVec]
  simp [coordDeriv,radialWeight_fderiv hx,axis,EuclideanSpace.inner_single_right,PiLp.smul_apply]

/-- The actual inverse-distance weight has a strictly positive radial plus
unit tangential Hessian sum at every point away from the center. -/
theorem radialWeight_strict_identity {c x : (X dim)} (hx : x ≠ c) :
    StrictMetricWeightAt (fun _ => (1 : (Mat dim))) (radialWeight c) x := by
  let d := x-c
  let q : ℝ := ‖d‖^2
  let t := q ^ (-(3/2):ℝ)
  let s := q ^ (-(5/2):ℝ)
  let b : (X dim) := (-t) • d
  let g : (MetricField dim) := fun _ => 1
  let φ := radialWeight c
  have hd : d ≠ 0 := sub_ne_zero.mpr hx
  have hq : 0 < q := pow_pos (norm_pos_iff.mpr hd) 2
  have ht : 0 < t := Real.rpow_pos_of_pos hq _
  have hm : s*q = t := by
    change q ^ (-(5/2):ℝ) * q = q ^ (-(3/2):ℝ)
    conv_lhs => arg 2; rw [← Real.rpow_one q]
    rw [← Real.rpow_add hq]
    norm_num
  have hgrad : chartMetricGradient g φ x = b := radialWeight_gradient hx
  have hb : b ≠ 0 := smul_ne_zero (neg_ne_zero.mpr ht.ne') hd
  have hcov : (fun i => coordDeriv i φ x) ≠ 0 := by
    intro h
    apply hb
    rw [← hgrad]
    change WithLp.toLp 2 (((1 : (Mat dim))⁻¹) *ᵥ (fun i => coordDeriv i φ x)) = 0
    rw [h,Matrix.mulVec_zero]
    rfl
  obtain ⟨D,hD,hDe⟩ := radialWeight_second hx
  have hD' (u v : (X dim)) : D u v = 3*s*⟪d,u⟫_ℝ*⟪d,v⟫_ℝ-t*⟪u,v⟫_ℝ := hDe u v
  have hn : metricPair g x b b = t^2 * q := by
    rw [metricPair_smul_same,metricPair_one]
    ring
  have hcovSq : covectorSq g φ x = t^2 * q := by
    rw [← metricPair_gradient_self g φ x Matrix.PosDef.one,hgrad,hn]
  refine ⟨hcov,fun v hunit hv => ?_⟩
  have horth : ⟪d,v⟫_ℝ = 0 := by
    rw [hgrad,metricPair_eq_dotProduct] at hv
    have hpair : ((fun i => d i) ⬝ᵥ (fun i => v i)) = ⟪d,v⟫_ℝ := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
      exact dotProduct_comm _ _
    have hh : -t * ⟪d,v⟫_ℝ = 0 := by
      rw [← hpair]
      rw [Matrix.one_mulVec] at hv
      change ((-t) • (fun i => d i)) ⬝ᵥ (fun i => v i) = 0 at hv
      simpa only [smul_dotProduct,smul_eq_mul] using hv
    exact (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr ht.ne')
  have hvv : ⟪v,v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq,← metricPair_one x]
    exact hunit
  have hbb : ⟪b,b⟫_ℝ = t^2*q := by
    rw [real_inner_self_eq_norm_sq,← metricPair_one x]
    exact hn
  have hdb : ⟪d,b⟫_ℝ = -t*q := by rw [show b = (-t) • d from rfl,real_inner_smul_right,real_inner_self_eq_norm_sq]
  rw [hgrad,hcovSq,identity_metricHessianEval hD,identity_metricHessianEval hD,hD',hD',
    horth,hvv,hbb,hdb]
  have he : 3*s*(-t*q)*(-t*q) - t*(t^2*q) = (2*t)*(t^2*q) := by
    calc
      _ = (3*(s*q)-t)*(t^2*q) := by ring
      _ = _ := by rw [hm]; ring
  rw [he,mul_div_cancel_right₀ _ (mul_pos (pow_pos ht _) hq).ne']
  linarith


open Carleman Carleman.Strict in
set_option maxHeartbeats 450000 in
/-- On a thin annulus a single shift can lie strictly between the
absolute tangential and positive radial Hessian eigenvalues. -/
theorem radialWeight_signed_criterion {c x : (X dim)} (hx : x ≠ c)
    {φ : (X dim) → ℝ} (hφ : ContDiff ℝ ∞ φ) (he : φ =ᶠ[𝓝 x] radialWeight c) {m : ℝ}
    (htan : (‖x-c‖^3)⁻¹ < m) (hnor : m < 2 * (‖x-c‖^3)⁻¹) :
    let A := fun (i j : (I dim)) (_ : (X dim)) => (1 : (Mat dim)) i j
    (∀ ξ : (I dim) → ℝ, ξ ≠ 0 → ∑ j, phaseField A φ j x * ξ j = 0 →
      0 < Mgrad A (phaseField A φ) x ξ + 4*m*quad A x ξ) ∧
      0 < 2 * ∑ j, phaseField A φ j x * pd j (phaseNorm A φ) x - 4*m*phaseNorm A φ x := by
  let A := fun (i j : (I dim)) (_ : (X dim)) => (1 : (Mat dim)) i j
  let d := x-c
  let q : ℝ := ‖d‖^2
  let t := q ^ (-(3/2):ℝ)
  let s := q ^ (-(5/2):ℝ)
  let b : (X dim) := (-t) • d
  have hr : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hq : 0 < q := pow_pos hr 2
  have ht : 0 < t := Real.rpow_pos_of_pos hq _
  have htp : t = (‖d‖^3)⁻¹ := by
    dsimp [t,q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le,
      show (↑(2 : ℕ) * -(3 / 2) : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg hr.le]
    norm_num [Real.rpow_natCast]
  have hm : s*q = t := by
    change q ^ (-(5/2):ℝ) * q = q ^ (-(3/2):ℝ)
    conv_lhs => arg 2; rw [← Real.rpow_one q]
    rw [← Real.rpow_add hq]
    norm_num
  have hA (i j : (I dim)) : ContDiff ℝ ∞ (A i j) := contDiff_const
  have hs (i j : (I dim)) : A i j = A j i := by
    funext y
    by_cases h : i = j <;> simp [A,Matrix.one_apply,h,Ne.symm]
  have hInv (r i j : (I dim)) : pd r (A i j) x = -∑ u, ∑ v, A i u x * pd r (A u v) x * A v j x := by
    simp [A,pd]
  have hsum (v : (I dim) → ℝ) (i : (I dim)) : ∑ j, A i j x * v j = v i := by
    simp [A,Matrix.one_apply]
  have hW (i : (I dim)) : phaseField A φ i x = b i := by
    change (∑ j, A i j x * pd j φ x) = b i
    rw [hsum]
    have hgrad := congrArg (fun u : (X dim) => u i) (radialWeight_gradient hx)
    change (∑ j, (1 : (Mat dim))⁻¹ i j * coordDeriv j (radialWeight c) x) = b i at hgrad
    rw [inv_one, hsum] at hgrad
    exact (congrArg (fun L : (X dim) →L[ℝ] ℝ => L (axis i)) (he.fderiv_eq (𝕜 := ℝ))).trans hgrad
  have hquad (v : (I dim) → ℝ) : quad A x v = ‖(WithLp.toLp 2 v : (X dim))‖ ^ 2 := by
    have hinner := real_inner_self_eq_norm_sq (WithLp.toLp 2 v : (X dim))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [quad,A,Matrix.one_apply,dotProduct,pow_two, mul_comm] using hinner
  have hN : phaseNorm A φ x = t^2*q := by
    change quad A x (fun i => pd i φ x) = _
    have hpd (i : (I dim)) : pd i φ x = b i := (hsum (fun i => pd i φ x) i).symm.trans (hW i)
    rw [hquad]
    simp only [hpd]
    change ‖b‖ ^ 2 = _
    rw [show b = (-t) • d from rfl, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
  obtain ⟨D,hD,hDe⟩ := radialWeight_second hx
  have hDφ : HasFDerivAt (fderiv ℝ φ) D x := hD.congr_of_eventuallyEq (he.fderiv (𝕜 := ℝ))
  have hH (u v : (X dim)) :
      (∑ i, ∑ j, christoffelHess A A φ x i j * u i * v j) =
        3*s*⟪d,u⟫_ℝ*⟪d,v⟫_ℝ - t*⟪u,v⟫_ℝ := by
    have hEq (i j : (I dim)) : christoffelHess A A φ x i j =
        metricHessian (fun _ => (1 : (Mat dim))) φ x i j := by
      simp [christoffelHess,A,pd,metricHessian,christoffel,hessian,coordDeriv,axis]
      rfl
    simp only [hEq]
    change metricHessianEval (fun _ => (1 : (Mat dim))) φ x u v = _
    rw [identity_metricHessianEval hDφ]
    exact hDe u v
  refine ⟨fun ξ hξ hker => ?_,?_⟩
  · let v : (X dim) := WithLp.toLp 2 ξ
    have hv (i : (I dim)) : v i = ξ i := rfl
    have hne : v ≠ 0 := fun h => hξ (congrArg WithLp.ofLp h)
    change (∑ j, phaseField A φ j x * ξ j) = 0 at hker
    simp only [hW, ← hv] at hker
    have horth : ⟪d,v⟫_ℝ = 0 := by
      have hab : ⟪b,v⟫_ℝ = 0 := by
        simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm] using hker
      rw [show b = (-t) • d from rfl, real_inner_smul_left] at hab
      exact (mul_eq_zero.mp hab).resolve_left (neg_ne_zero.mpr ht.ne')
    have hM := Mgrad_inverse_eq_hess hA hφ hs x hInv ξ ξ (fun i => (hsum ξ i).symm)
    rw [hM,hquad]
    simp only [← hv,hH,horth,real_inner_self_eq_norm_sq]
    have hpos := mul_pos (sub_pos.mpr (htp.trans_lt htan)) (pow_pos (norm_pos_iff.mpr hne) 2)
    nlinarith only [hpos]
  · change 0 < 2 * (∑ j, phaseField A φ j x * pd j (phaseNorm A φ) x) -
        4*m*phaseNorm A φ x
    rw [phaseField_dot_pd_phaseNorm hA hφ hs x hInv,hN]
    simp only [hW,hH]
    have hdb : ⟪d,b⟫_ℝ = -t*q := by
      rw [show b = (-t) • d from rfl,real_inner_smul_right,real_inner_self_eq_norm_sq]
    have hbb : ⟪b,b⟫_ℝ = t^2*q := by
      rw [real_inner_self_eq_norm_sq,show b = (-t) • d from rfl, norm_smul, Real.norm_eq_abs,
        mul_pow,sq_abs,neg_sq]
    rw [hdb,hbb]
    have heq : 3*s*(-t*q)*(-t*q) - t*(t^2*q) = (2*t)*(t^2*q) := by
      calc
        _ = (3*(s*q)-t)*(t^2*q) := by ring
        _ = _ := by rw [hm]; ring
    rw [heq]
    have hpos := mul_pos (sub_pos.mpr (by simpa only [htp] using hnor) : 0 < 2*t-m)
      (mul_pos (pow_pos ht 2) hq)
    nlinarith only [hpos]

end CalderonN.FixedTube
