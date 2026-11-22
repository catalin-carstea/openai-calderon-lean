module

public import Proof.CalderonN.SmoothSphereRotationProjection
public import Proof.CalderonN.HorizontalRepresentative
public import Proof.CalderonN.FischerFields

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

section FiniteFields

variable {ι : Type*} [Fintype ι]

def finitePolynomialSphereMap (b : ι → MvPolynomial (Fin N) ℝ) :
    (ι → ℝ) →L[ℝ] (SphereL2 N) :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (polynomialSphereL2 (b j))

lemma finitePolynomialSphereMap_apply (b : ι → MvPolynomial (Fin N) ℝ)
    (c : (X N) → ι → ℝ) (x : (X N)) :
    finitePolynomialSphereMap b (c x) = polynomialSphereL2 (finitePolynomialField b c x) := by
  simp [finitePolynomialSphereMap,finitePolynomialField,map_sum,map_smul]

lemma contDiff_polynomialSphereL2_finite (b : ι → MvPolynomial (Fin N) ℝ)
    (c : (X N) → ι → ℝ) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun x => polynomialSphereL2 (finitePolynomialField b c x)) := by
  simpa only [Function.comp_def,finitePolynomialSphereMap_apply] using
    (finitePolynomialSphereMap b).contDiff.comp hc

lemma fderiv_polynomialSphereL2_finite (b : ι → MvPolynomial (Fin N) ℝ)
    (c : (X N) → ι → ℝ) (hc : ContDiff ℝ ∞ c) (x a : (X N)) :
    fderiv ℝ (fun y => polynomialSphereL2 (finitePolynomialField b c y)) x a =
      polynomialSphereL2 (finitePolynomialFieldDerivative b c x a) := by
  have h := ((finitePolynomialSphereMap b).hasFDerivAt.comp x
    (hc.differentiable (by simp) x).hasFDerivAt).fderiv
  have heq : (fun y => finitePolynomialSphereMap b (c y)) =
      fun y => polynomialSphereL2 (finitePolynomialField b c y) := by
    funext y; exact finitePolynomialSphereMap_apply b c y
  change fderiv ℝ (fun y => finitePolynomialSphereMap b (c y)) x = _ at h
  rw [heq] at h
  rw [h,ContinuousLinearMap.comp_apply]
  simp [finitePolynomialSphereMap,finitePolynomialFieldDerivative,map_sum,map_smul]

 
lemma polynomialSphereL2_finite_derivative_eq (k : ℕ)
    (b : ι → MvPolynomial (Fin N) ℝ) (c : (X N) → ι → ℝ)
    (U : (X N) → harmonicSphereSubspace N k) (hc : ContDiff ℝ ∞ c)
    (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : (SphereL2 N)))
    (x a : (X N)) :
    polynomialSphereL2 (finitePolynomialFieldDerivative b c x a) =
      (fderiv ℝ U x a : (SphereL2 N)) := by
  have heq : (fun y => polynomialSphereL2 (finitePolynomialField b c y)) =
      fun y => (U y : (SphereL2 N)) := funext hrep
  rw [← fderiv_polynomialSphereL2_finite b c hc x a,heq]
  have h := ((harmonicSphereSubspace N k).subtypeL.hasFDerivAt.comp x
    (hU.differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun A : (X N) →L[ℝ] (SphereL2 N) => A a) h

lemma polynomialSphereL2_rotation_eq (k : ℕ) (i j : Fin N)
    (p : MvPolynomial (Fin N) ℝ) (hp : p ∈ harmonicHomogeneous N k)
    (v : harmonicSphereSubspace N k) (hrep : polynomialSphereL2 p = (v : (SphereL2 N))) :
    polynomialSphereL2 (polynomialRotation i j p) =
      (harmonicSphereRotation k i j v : (SphereL2 N)) := by
  have hv : harmonicPolynomialSphereMap k ⟨p,hp⟩ = v := by
    apply Subtype.ext; exact hrep
  rw [← hv,harmonicSphereRotation_apply_image]
  rfl

end FiniteFields

lemma polynomialConnectionAction_eq_rotations (A : (I N) → (I N) → ℝ) (hA : ∀ i j,A i j = -A j i)
    (p : MvPolynomial (I N) ℝ) :
    polynomialConnectionAction A p = ∑ i,∑ j,(-(1/2 : ℝ)*A i j) • polynomialRotation i j p := by
  have hswap :
      (∑ i, ∑ j, C (-(1/2 : ℝ)*A i j) * (MvPolynomial.X j * pderiv i p)) =
        -(∑ i, ∑ j, C (-(1/2 : ℝ)*A i j) * (MvPolynomial.X i * pderiv j p)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib, ← neg_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA j i, ← map_neg]
    congr 2
    ring
  simp only [polynomialRotation, smul_eq_C_mul, mul_sub, Finset.sum_sub_distrib, hswap,
    sub_neg_eq_add]
  rw [← Finset.sum_add_distrib]
  unfold polynomialConnectionAction
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_mul, ← map_add]
  congr 2
  ring


def harmonicCovariantDerivative (g : (MetricField N)) (e : (Frame N)) (k : ℕ)
    (U : (X N) → harmonicSphereSubspace N k) (y a : (X N)) : harmonicSphereSubspace N k :=
  fderiv ℝ U y a + ∑ i,∑ j,(-(1/2 : ℝ)*frameConnectionCoefficient g e y a i j) •
    harmonicSphereRotation k i j (U y)

/-- The actual finite polynomial covariant derivative is the intrinsic Hilbert harmonic
    covariant derivative for any smooth orthonormal frame and metric. -/
theorem polynomialSphereL2_covariantDerivative {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {ι : Type*} [Fintype ι] (k : ℕ) (b : ι → MvPolynomial (I N) ℝ) (hb : ∀ j,b j ∈ harmonicHomogeneous N k)
    (c : (X N) → ι → ℝ) (U : (X N) → harmonicSphereSubspace N k)
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ y,polynomialSphereL2 (finitePolynomialField b c y) = (U y : (SphereL2 N)))
    {y : (X N)} (hy : y ∈ Y) (a : (X N)) :
    polynomialSphereL2 (covariantPolynomialDerivative g e b c y a) =
      (harmonicCovariantDerivative g e k U y a : (SphereL2 N)) := by
  rw [covariantPolynomialDerivative,map_add,
    polynomialSphereL2_finite_derivative_eq k b c U hc hU hrep y a,
    polynomialConnectionAction_eq_rotations _ (frameConnection_skew hY h hK e he hframe hy a)]
  have hrot (i j : (I N)) := polynomialSphereL2_rotation_eq k i j
    (finitePolynomialField b c y) (show finitePolynomialField b c y ∈ harmonicHomogeneous N k from
      ⟨finitePolynomialField_homogeneous b (fun j => (hb j).1) c y,
        finitePolynomialField_harmonic b (fun j => (hb j).2) c y⟩) (U y) (hrep y)
  simp only [map_sum,map_smul,hrot,harmonicCovariantDerivative,Submodule.coe_add,Submodule.coe_sum,Submodule.coe_smul]

end CalderonN
