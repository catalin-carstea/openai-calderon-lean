import Proof.FrameDuality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace

noncomputable section
open Set
namespace ShrinkingSpheres

lemma frame_linearIndependent (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    LinearIndependent ℝ (e y) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hh := congrArg (fun v => metricPair g y v (e y j)) hc
  rw [metricPair_sum_left] at hh
  have hz : metricPair g y (0:X) (e y j) = 0 := by simp [metricPair]
  rw [hz] at hh
  simp only [metricPair_smul_left, he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at hh
  exact hh

/-- The orthonormal frame as an ordinary basis, for coordinate-independent traces. -/
def frameBasis (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    Module.Basis I ℝ X :=
  basisOfLinearIndependentOfCardEqFinrank (frame_linearIndependent g e y he) (by simp [X, I])

lemma frameBasis_apply (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (i : I) :
    frameBasis g e y he i = e y i := by simp [frameBasis]

lemma frameBasis_repr (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (v : X) (i : I) :
    (frameBasis g e y he).repr v i = metricPair g y v (e y i) := by
  have hv : (∑ j, (frameBasis g e y he).repr v j • e y j) = v := by
    simpa only [frameBasis_apply] using (frameBasis g e y he).sum_repr v
  have hh := congrArg (fun w => metricPair g y w (e y i)) hv
  rw [metricPair_sum_left] at hh
  simpa only [metricPair_smul_left, he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hh

/-- The trace of a tangent endomorphism in an orthonormal frame is its coordinate trace. -/
lemma metric_frame_endomorphism_trace (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (A : X →L[ℝ] X) :
    (∑ i, metricPair g y (A (e y i)) (e y i)) = ∑ i, (A (axis i)) i := by
  have hh := congrArg (fun T : (X →ₗ[ℝ] X) →ₗ[ℝ] ℝ => T A.toLinearMap)
    (LinearMap.traceAux_eq ℝ (frameBasis g e y he) (PiLp.basisFun 2 ℝ I))
  simpa only [LinearMap.traceAux_def, Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    frameBasis_apply, frameBasis_repr, PiLp.basisFun_apply, PiLp.basisFun_repr,
    axis, EuclideanSpace.single, ContinuousLinearMap.coe_coe] using hh

end ShrinkingSpheres
