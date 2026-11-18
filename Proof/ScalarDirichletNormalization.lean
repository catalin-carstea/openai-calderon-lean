import Proof.StrongPoissonPerturbation
import Proof.FirstRadialOrderZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The scalar inverse algebra, abstracted from the supplied local constant
    metric-scaling proof, works between different Banach operator spaces. -/
theorem clm_inverse_const_smul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (c : ℝ) (hc : c ≠ 0) (hA : A.IsInvertible) :
    (c • A).IsInvertible ∧ (c • A).inverse = c⁻¹ • A.inverse := by
  have hLeft : (c • A).comp (c⁻¹ • A.inverse) = ContinuousLinearMap.id ℝ F := by
    ext z
    simp only [ContinuousLinearMap.comp_apply,_root_.smul_apply,map_smul,smul_smul,
      hA.self_apply_inverse,inv_mul_cancel₀ hc,one_smul,ContinuousLinearMap.id_apply]
  have hRight : (c⁻¹ • A.inverse).comp (c • A) = ContinuousLinearMap.id ℝ E := by
    ext z
    simp only [ContinuousLinearMap.comp_apply,_root_.smul_apply,map_smul,smul_smul,
      hA.inverse_apply_self,mul_inv_cancel₀ hc,one_smul,ContinuousLinearMap.id_apply]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hLeft hRight,ContinuousLinearMap.inverse_eq hLeft hRight⟩

/-- Multiplying a divergence coefficient by a nonzero spatially constant
    scalar preserves the genuine strong Dirichlet Poisson solution. -/
theorem strongPoissonL_const_smul (F : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : c ≠ 0)
    (hF : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible) :
    (strongDirichletOperator fixedSobolevCalculus 0 (c • F)).IsInvertible ∧
      strongPoissonL (c • F) = strongPoissonL F := by
  have hA : strongDirichletOperator fixedSobolevCalculus 0 (c • F) =
      c • strongDirichletOperator fixedSobolevCalculus 0 F := by
    change (strongCoefficientOperatorL fixedSobolevCalculus 0) (c • F) =
      c • (strongCoefficientOperatorL fixedSobolevCalculus 0) F
    exact (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul c F
  have hScaled := clm_inverse_const_smul (strongDirichletOperator fixedSobolevCalculus 0 F) c hc hF
  refine ⟨hA ▸ hScaled.1,?_⟩
  apply ContinuousLinearMap.ext
  intro f
  rw [strongPoissonL_apply,strongPoissonL_apply,hA,hScaled.2]
  simp only [(fullCoefficientOperatorL fixedSobolevCalculus 0).map_smul,
    _root_.smul_apply,map_smul,smul_smul,mul_inv_cancel₀ hc,one_smul]

/-- The actual high radial error is invariant under the same constant
    coefficient scaling, including a center-dependent scalar frozen per ball. -/
theorem actualHighRadialErrorL_const_smul (F : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : c ≠ 0)
    (hF : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible) :
    actualHighRadialErrorL (c • F) = actualHighRadialErrorL F := by
  have hP := (strongPoissonL_const_smul F c hc hF).2
  exact congrArg (fun Q => fixedHalfOutwardTraceL.comp Q-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL) hP

end ShrinkingSpheres
