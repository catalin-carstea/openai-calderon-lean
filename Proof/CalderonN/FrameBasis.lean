module

public import Proof.CalderonN.FrameDuality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

@[expose] public section

/- Port of FrameBasis.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

lemma frame_linearIndependent (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    LinearIndependent ℝ (e y) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hh := congrArg (fun v => metricPair g y v (e y j)) hc
  rw [metricPair_sum_left] at hh
  have hz : metricPair g y (0:(X n)) (e y j) = 0 := by simp [metricPair]
  rw [hz] at hh
  simp only [metricPair_smul_left, he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hh
  exact hh

variable [NeZero n]

/-- The orthonormal frame as an ordinary basis, for coordinate-independent traces. -/
def frameBasis (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    Module.Basis (I n) ℝ (X n) :=
  basisOfLinearIndependentOfCardEqFinrank (frame_linearIndependent g e y he) (by simp [X, I])

lemma frameBasis_apply (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (i : (I n)) :
    frameBasis g e y he i = e y i := by simp [frameBasis]

lemma frameBasis_repr (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (v : (X n)) (i : (I n)) :
    (frameBasis g e y he).repr v i = metricPair g y v (e y i) := by
  have hv : (∑ j, (frameBasis g e y he).repr v j • e y j) = v := by
    simpa only [frameBasis_apply] using (frameBasis g e y he).sum_repr v
  have hh := congrArg (fun w => metricPair g y w (e y i)) hv
  rw [metricPair_sum_left] at hh
  simpa only [metricPair_smul_left, he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hh

/-- The trace of a tangent endomorphism in an orthonormal frame is its coordinate trace. -/
lemma metric_frame_endomorphism_trace (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (A : (X n) →L[ℝ] (X n)) :
    (∑ i, metricPair g y (A (e y i)) (e y i)) = ∑ i, (A (axis i)) i := by
  have hh := congrArg (fun T : ((X n) →ₗ[ℝ] (X n)) →ₗ[ℝ] ℝ => T A.toLinearMap)
    (LinearMap.traceAux_eq ℝ (frameBasis g e y he) (PiLp.basisFun 2 ℝ (I n)))
  simpa only [LinearMap.traceAux_def, Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    frameBasis_apply, frameBasis_repr, PiLp.basisFun_apply, PiLp.basisFun_repr,
    axis, EuclideanSpace.single, ContinuousLinearMap.coe_coe] using hh

end CalderonN
