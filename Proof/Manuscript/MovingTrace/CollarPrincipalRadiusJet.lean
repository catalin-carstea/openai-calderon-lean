module

public import Proof.Manuscript.MovingTrace.SphericalNormalCollar
public import Proof.CalderonPatch.BoundaryRootDerivative
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

open CalderonN CalderonPatch Set
open scoped ContDiff Matrix.Norms.Operator

namespace CalderonPaper

variable {dim d : ℕ} [NeZero dim]

local instance matrixCurveTopology : TopologicalSpace (Mat d) :=
  @NormedAddCommGroup.toMetricSpace (Mat d) Matrix.linftyOpNormedAddCommGroup
    |>.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The metric in the tangential block of the rescaled spherical collar. -/
def collarTangentialMetric (g : MetricField dim) (sphereChart : X d → X dim)
    (q : X d × ℝ) : Mat d :=
  fun i j => metricPair g (polarCollar sphereChart q)
    (fderiv ℝ (polarCollar sphereChart) q (axis i,0))
    (fderiv ℝ (polarCollar sphereChart) q (axis j,0))

/-- Rescaling the geodesic normal map does not vary the tangent metric of
the spherical collar to first order in the radius at zero. -/
theorem collarTangentialMetric_first_radius_zero
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {γ : MetricField dim} (hEll : Elliptic Ω K γ) (hK : 0 < K)
    {E : X dim × X dim → X dim} {R : X dim → ℝ}
    (hNormal : NormalCoordinates Y Ω γ E R) {y : X dim} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : Frame dim) (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (sphereChart : X d → X dim) (q : X d × ℝ) :
    HasDerivAt (fun r : ℝ => collarTangentialMetric (framedNormalMetric γ e E y r) sphereChart q) 0 0 := by
  let z := polarCollar sphereChart q
  let A := fun r : ℝ => collarTangentialMetric (framedNormalMetric γ e E y r) sphereChart q
  have hEntry (i j : I d) : HasDerivAt (fun r => A r i j) 0 0 := by
    let u := fderiv ℝ (polarCollar sphereChart) q (axis i, 0)
    let v := fderiv ℝ (polarCollar sphereChart) q (axis j, 0)
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
        ((hNormal.framedNormalMetric_first_zero hΩ hEll hK hy hyΩ e he z k l).mul_const
          (u k)).mul_const (v l)
    simpa only [A, collarTangentialMetric, z, u, v, metricPair, zero_mul, Finset.sum_const_zero] using h
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (hEntry i j).smul_const (Matrix.single i j (1 : ℝ) : Mat d)
  have hRewrite (r : ℝ) :
      (∑ i : I d, ∑ j : I d, A r i j • (Matrix.single i j (1 : ℝ) : Mat d)) = A r := by
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.sum_sum_single (A r)
  simpa only [hRewrite, zero_smul, Finset.sum_const_zero] using h

/-- The actual positive collar root at nonzero tangential covector has
zero first radius derivative. This is the principal-order cancellation
needed before expanding the radial trace in the symbol topology. -/
theorem collarBoundaryRoot_first_radius_zero
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {γ : MetricField dim} (hEll : Elliptic Ω K γ) (hK : 0 < K)
    {E : X dim × X dim → X dim} {R : X dim → ℝ}
    (hNormal : NormalCoordinates Y Ω γ E R) {y : X dim} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : Frame dim) (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (sphereChart : X d → X dim) (q : X d × ℝ)
    (hp : (collarTangentialMetric (framedNormalMetric γ e E y 0) sphereChart q).PosDef)
    {ξ : X d} (hξ : ξ ≠ 0) :
    HasDerivAt (fun r : ℝ =>
      boundaryRoot (collarTangentialMetric (framedNormalMetric γ e E y r) sphereChart q) ξ) 0 0 := by
  have hj := collarTangentialMetric_first_radius_zero hΩ hEll hK hNormal hy hyΩ e he sphereChart q
  simpa only [metricPair, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero, zero_div] using
    hasDerivAt_boundaryRoot hj hp hξ

end CalderonPaper
