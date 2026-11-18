import Proof.Archive.NativeOrthogonalCoefficientEnergyCovariance
import Proof.PositiveCoefficientScaling

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.MetricOperator

lemma matrixBilinearForm_orthogonal_coefficient (e : X ≃ₗᵢ[ℝ] X) (a : X → Mat) (x η ξ : X) :
    TauCeti.PDE.matrixBilinearForm (orthogonalPrincipalCoefficient e a x) η ξ =
      TauCeti.PDE.matrixBilinearForm (a (e x)) (e η) (e ξ) := by
  have hMap : matrixOperatorMap (orthogonalPrincipalCoefficient e a x) ξ =
      e.symm (matrixOperatorMap (a (e x)) (e ξ)) := by
    change (operatorMatrixMap _).toEuclideanLin ξ = _
    rw [operatorMatrixMap_apply]
    rfl
  rw [matrixBilinearForm_eq_matrixOperator_inner,matrixBilinearForm_eq_matrixOperator_inner,hMap]
  simpa only [e.symm_apply_apply] using
    e.symm.inner_map_map (matrixOperatorMap (a (e x)) (e ξ)) (e η)

/-- Orthogonal changes of normal coordinates retain the actual ellipticity
constants, in the same Euclidean unit ball. -/
theorem uniformlyEllipticOn_orthogonal_unitBall (e : X ≃ₗᵢ[ℝ] X)
    (a : X → Mat) (lam Lam : ℝ)
    (h : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) a lam Lam) :
    TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (orthogonalPrincipalCoefficient e a) lam Lam := by
  refine ⟨h.1,h.2.1,?_⟩
  intro x hx
  have hex : e x ∈ (ballOpens:Set X) := by
    change e x ∈ Metric.ball (0:X) 1
    have hxB : x ∈ Metric.ball (0:X) 1 := hx
    simpa only [Metric.mem_ball,dist_zero_right,e.norm_map] using hxB
  constructor
  · intro ξ
    rw [← TauCeti.PDE.matrixBilinearForm_self,matrixBilinearForm_orthogonal_coefficient,
      TauCeti.PDE.matrixBilinearForm_self]
    simpa only [e.norm_map] using (h.2.2 hex).1 (e ξ)
  · intro η ξ
    rw [← TauCeti.PDE.matrixBilinearForm_apply,matrixBilinearForm_orthogonal_coefficient,
      TauCeti.PDE.matrixBilinearForm_apply]
    simpa only [e.norm_map] using (h.2.2 hex).2 (e η) (e ξ)

lemma orthogonalPrincipalCoefficient_isSymm (e : X ≃ₗᵢ[ℝ] X) (a : X → Mat) (x : X)
    (h : (a (e x)).IsSymm) : (orthogonalPrincipalCoefficient e a x).IsSymm := by
  rw [orthogonalPrincipalCoefficient_eq_matrix_conjugation]
  change (a (e x)).transpose = a (e x) at h
  let Q : Mat := operatorMatrixMap e.toContinuousLinearEquiv.toContinuousLinearMap
  change (Q.transpose*a (e x)*Q).transpose = Q.transpose*a (e x)*Q
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,h,Matrix.mul_assoc]

end ShrinkingSpheres
