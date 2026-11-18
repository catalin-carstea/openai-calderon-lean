import Proof.NativeWeakInverseBound
import Proof.Archive.NativeOrthogonalCoefficientEnergyCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped Matrix.Norms.Elementwise InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.ConnectionError OAI.AnisotropicCalderon.MetricOperator

lemma matrixBilinearForm_orthogonal_coefficient (e : X ≃ₗᵢ[ℝ] X) (a : X → Mat) (z u v : X) :
    TauCeti.PDE.matrixBilinearForm (orthogonalPrincipalCoefficient e a z) u v =
      TauCeti.PDE.matrixBilinearForm (a (e z)) (e u) (e v) := by
  rw [matrixBilinearForm_eq_matrixOperator_inner,matrixBilinearForm_eq_matrixOperator_inner]
  have hMap : matrixOperatorMap (orthogonalPrincipalCoefficient e a z) v =
      e.symm (matrixOperatorMap (a (e z)) (e v)) := by
    change (operatorMatrixMap _).toEuclideanLin v = _
    rw [operatorMatrixMap_apply]
    rfl
  rw [hMap]
  simpa only [e.symm_apply_apply] using
    e.symm.inner_map_map (matrixOperatorMap (a (e z)) (e v)) (e u)

/-- Rotation preserves the exact weak ellipticity constants on the ball. -/
theorem uniformlyEllipticOn_unitBall_orthogonal (e : X ≃ₗᵢ[ℝ] X) (a : X → Mat) (lam Lam : ℝ)
    (h : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) a lam Lam) :
    TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (orthogonalPrincipalCoefficient e a) lam Lam := by
  refine ⟨h.1,h.2.1,?_⟩
  intro z hz
  have hez : e z ∈ (ballOpens:Set X) := by
    change z ∈ e ⁻¹' (ballOpens:Set X)
    rw [orthogonal_preimage_unitBall]
    exact hz
  have hAt := h.2.2 hez
  constructor
  · intro u
    have hQ := matrixBilinearForm_orthogonal_coefficient e a z u u
    rw [TauCeti.PDE.matrixBilinearForm_self,TauCeti.PDE.matrixBilinearForm_self] at hQ
    rw [hQ]
    simpa only [e.norm_map] using hAt.1 (e u)
  · intro u v
    have hQ := matrixBilinearForm_orthogonal_coefficient e a z u v
    rw [TauCeti.PDE.matrixBilinearForm_apply,TauCeti.PDE.matrixBilinearForm_apply] at hQ
    rw [hQ]
    simpa only [e.norm_map] using hAt.2 (e u) (e v)

end ShrinkingSpheres
