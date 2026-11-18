import Proof.MovingFrameSecond
import Proof.CoarseValueAlgebra
import Proof.FrameAdjointOperators
import Proof.UniformFirstAdjointTaylor
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
theorem coarseValue_sum_three (u : I → SphereSobolev 0) (f : I → UnitSphere → ℝ)
    (h : ∀ i,(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (u i)
      =ᵐ[sphereProbability] f i) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (∑ i : I,u i)
      =ᵐ[sphereProbability] fun w => ∑ i : I,f i w := by
  simpa only [Fin.sum_univ_three] using
    coarseValue_add (u 0+u 1) (u 2) (fun w => f 0 w+f 1 w) (f 2)
      (coarseValue_add (u 0) (u 1) (f 0) (f 1) (h 0) (h 1)) (h 2)

theorem coarseValue_weighted_sum_three (c : I → ℝ) (u : I → SphereSobolev 0) (f : I → UnitSphere → ℝ)
    (h : ∀ i,(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (u i)
      =ᵐ[sphereProbability] f i) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (∑ i : I,c i • u i)
      =ᵐ[sphereProbability] fun w => ∑ i : I,c i*f i w :=
  coarseValue_sum_three (fun i => c i • u i) (fun i w => c i*f i w)
    (fun i => coarseValue_smul (c i) (u i) (f i) (h i))

def frameAdjointField (A : TraceAdjoint) (e : Frame) (i : I) (φ : Field) : Field :=
  fun p => ∑ a : I,e p.1 i a • adjointField A a φ p

theorem frameTraceDerivative_eq_horizontal_adjoint (g : MetricField) (A : TraceAdjoint)
    (e : Frame) (i : I) (φ : Field) (y w : X) :
    frameTraceDerivative g A e i φ (y,w) =
      horizontal g φ y w (e y i)+frameAdjointField A e i φ (y,w) := by
  rw [frameTraceDerivative_apply]
  simp only [traceDerivative,smul_add,Finset.sum_add_distrib,frameAdjointField]
  congr 1
  have h := congrArg (horizontalBaseL g φ y w) (axis_expansion (e y i))
  simpa only [map_sum,map_smul,horizontalBaseL_apply] using h


theorem Elliptic.frame_component_abs_le {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 1 ≤ K) (e : Frame) {y : X} (hy : y ∈ Ω)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (i a : I) :
    |e y i a| ≤ K := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hSphere : e y i ∈ sphereAt g y := by
    exact (hframe i i).trans (ite_eq_left_iff.mpr (fun h => False.elim (h rfl)))
  have hSq := h.sphere_norm_sq_bound hKpos hy hSphere
  have hNorm : ‖e y i‖ ≤ K := by
    apply (sq_le_sq₀ (norm_nonneg _) hKpos.le).mp
    nlinarith only [hSq,hK,sq_nonneg (K-1)]
  have hCoord : |e y i a| ≤ ‖e y i‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e y i) a
  exact hCoord.trans hNorm

theorem norm_weighted_sum_three_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : I → ℝ) (F : I → E) (K q : ℝ) (hK : 0 ≤ K)
    (hc : ∀ i,|c i| ≤ K) (hF : ∀ i,‖F i‖ ≤ q) :
    ‖∑ i : I,c i • F i‖ ≤ 3*K*q := by
  calc
    _ ≤ ∑ i : I,‖c i • F i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I,K*q := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hc i) (hF i) (norm_nonneg _) hK
    _ = _ := by simp only [Fin.sum_univ_three];ring

theorem frame_adjoint_operator_realization (d : Data) (y : X) (i : I)
    (T : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (φ : Field) (L : ℂ →L[ℝ] ℝ) (v : SphereSobolev 1)
    (hT : ∀ a,(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (T a v)
      =ᵐ[sphereProbability] fun w : UnitSphere => L (adjointField d.adjoint a φ (y,frameVector d.frame y w.val))) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      ((∑ a : I,d.frame y i a • T a) v) =ᵐ[sphereProbability]
      fun w : UnitSphere => L (frameAdjointField d.adjoint d.frame i φ (y,frameVector d.frame y w.val)) := by
  have hh := coarseValue_weighted_sum_three (fun a => d.frame y i a) (fun a => T a v)
    (fun a w => L (adjointField d.adjoint a φ (y,frameVector d.frame y w.val))) hT
  simpa only [_root_.sum_apply,_root_.smul_apply,frameAdjointField,map_sum,map_smul,smul_eq_mul] using hh
end ShrinkingSpheres
