module

public import Proof.CalderonN.DensityDivergence
public import Proof.CalderonN.ProfileHessian
import Mathlib.Tactic

@[expose] public section

/- Port of HessianDifferential.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set


lemma covJet_one (g : (MetricField n)) (f : (X n) → ℝ) (y : (X n)) (i : (I n)) :
    covJet g f 1 y ![i] = coordDeriv i f y := by simp [covJet]

lemma covJet_two (g : (MetricField n)) (f : (X n) → ℝ) (y : (X n)) (i j : (I n)) :
    covJet g f 2 y ![i,j] = coordDeriv i (coordDeriv j f) y -
      ∑ k, christoffel g y k i j * coordDeriv k f y := by
  simp [covJet, Fin.sum_univ_one]

lemma coordinate_second_derivative (f : (X n) → ℝ) (y : (X n))
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) (i j : (I n)) :
    coordDeriv i (coordDeriv j f) y = fderiv ℝ (fderiv ℝ f) y (axis i) (axis j) := by
  change fderiv ℝ (fun x => fderiv ℝ f x (axis j)) y (axis i) = _
  have hh := hf.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) (axis j) y)
  have he := congrArg (fun L : (X n) →L[ℝ] ℝ => L (axis i)) hh.fderiv
  simpa only [coordDeriv, _root_.add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, add_zero, zero_add, ContinuousLinearMap.flip_apply] using he

lemma derivative_covector_apply (f : (X n) → ℝ) (y a v : (X n))
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) :
    fderiv ℝ (fun x => fderiv ℝ f x v) y a = fderiv ℝ (fderiv ℝ f) y a v := by
  have hh := hf.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) v y)
  have he := congrArg (fun L : (X n) →L[ℝ] ℝ => L a) hh.fderiv
  simpa only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, add_zero, zero_add, ContinuousLinearMap.flip_apply] using he

/-- The coordinate Hessian as a bilinear form with the connection correction included. -/
def hessianBilinear (g : (MetricField n)) (f : (X n) → ℝ) (y : (X n)) : (X n) →L[ℝ] (X n) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) y -
    ((ContinuousLinearMap.compL ℝ (X n) (X n) ℝ) (fderiv ℝ f y)).comp (connectionBilinear g y)

lemma hessianBilinear_apply (g : (MetricField n)) (f : (X n) → ℝ) (y u v : (X n)) :
    hessianBilinear g f y u v = fderiv ℝ (fderiv ℝ f) y u v - fderiv ℝ f y (connection g y u v) := by
  simp [hessianBilinear, connectionBilinear_apply]

lemma hessianBilinear_axes (g : (MetricField n)) (f : (X n) → ℝ) (y : (X n))
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) (i j : (I n)) :
    hessianBilinear g f y (axis i) (axis j) = covJet g f 2 y ![i,j] := by
  rw [hessianBilinear_apply, covJet_two, coordinate_second_derivative f y hf]
  congr 1
  rw [linear_axis_expansion]
  simp_rw [connection_axis_components]
  apply Finset.sum_congr rfl
  intro k _
  rfl

lemma bilinear_axis_expansion (B : (X n) →L[ℝ] (X n) →L[ℝ] ℝ) (u v : (X n)) :
    B u v = ∑ i, ∑ j, u i * v j * B (axis i) (axis j) := by
  conv_lhs => rw [← axis_expansion u, ← axis_expansion v]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma hessianBilinear_eq_coordinate (g : (MetricField n)) (f : (X n) → ℝ) (y : (X n))
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) (u v : (X n)) :
    hessianBilinear g f y u v = metricPair (hessianMatrix g f) y u v := by
  rw [bilinear_axis_expansion]
  simp_rw [hessianBilinear_axes g f y hf]
  unfold metricPair hessianMatrix
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end CalderonN
