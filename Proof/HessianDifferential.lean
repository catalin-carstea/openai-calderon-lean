import Proof.DensityDivergence
import Proof.ProfileHessian

noncomputable section
open Set
namespace ShrinkingSpheres

lemma covJet_one (g : MetricField) (f : X → ℝ) (y : X) (i : I) :
    covJet g f 1 y ![i] = coordDeriv i f y := by simp [covJet]

lemma covJet_two (g : MetricField) (f : X → ℝ) (y : X) (i j : I) :
    covJet g f 2 y ![i,j] = coordDeriv i (coordDeriv j f) y -
      ∑ k, christoffel g y k i j * coordDeriv k f y := by
  simp [covJet, Fin.sum_univ_one]

lemma coordinate_second_derivative (f : X → ℝ) (y : X)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) (i j : I) :
    coordDeriv i (coordDeriv j f) y = fderiv ℝ (fderiv ℝ f) y (axis i) (axis j) := by
  change fderiv ℝ (fun x => fderiv ℝ f x (axis j)) y (axis i) = _
  have hh := hf.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) (axis j) y)
  have he := congrArg (fun L : X →L[ℝ] ℝ => L (axis i)) hh.fderiv
  simpa only [coordDeriv, _root_.add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, add_zero, zero_add, ContinuousLinearMap.flip_apply] using he

lemma derivative_covector_apply (f : X → ℝ) (y a v : X)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) :
    fderiv ℝ (fun x => fderiv ℝ f x v) y a = fderiv ℝ (fderiv ℝ f) y a v := by
  have hh := hf.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℝ) v y)
  have he := congrArg (fun L : X →L[ℝ] ℝ => L a) hh.fderiv
  simpa only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, add_zero, zero_add, ContinuousLinearMap.flip_apply] using he

/-- The coordinate Hessian as a bilinear form with the connection correction included. -/
def hessianBilinear (g : MetricField) (f : X → ℝ) (y : X) : X →L[ℝ] X →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) y -
    ((ContinuousLinearMap.compL ℝ X X ℝ) (fderiv ℝ f y)).comp (connectionBilinear g y)

lemma hessianBilinear_apply (g : MetricField) (f : X → ℝ) (y u v : X) :
    hessianBilinear g f y u v = fderiv ℝ (fderiv ℝ f) y u v - fderiv ℝ f y (connection g y u v) := by
  simp [hessianBilinear, connectionBilinear_apply]

lemma hessianBilinear_axes (g : MetricField) (f : X → ℝ) (y : X)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) (i j : I) :
    hessianBilinear g f y (axis i) (axis j) = covJet g f 2 y ![i,j] := by
  rw [hessianBilinear_apply, covJet_two, coordinate_second_derivative f y hf]
  congr 1
  rw [linear_axis_expansion]
  simp_rw [connection_axis_components]
  apply Finset.sum_congr rfl
  intro k _
  rfl

lemma bilinear_axis_expansion (B : X →L[ℝ] X →L[ℝ] ℝ) (u v : X) :
    B u v = ∑ i, ∑ j, u i * v j * B (axis i) (axis j) := by
  conv_lhs => rw [← axis_expansion u, ← axis_expansion v]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma hessianBilinear_eq_coordinate (g : MetricField) (f : X → ℝ) (y : X)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) y) (u v : X) :
    hessianBilinear g f y u v = metricPair (hessianMatrix g f) y u v := by
  rw [bilinear_axis_expansion]
  simp_rw [hessianBilinear_axes g f y hf]
  unfold metricPair hessianMatrix
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ShrinkingSpheres
