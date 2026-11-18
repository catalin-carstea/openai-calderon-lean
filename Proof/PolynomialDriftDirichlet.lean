import Proof.Archive.NativePolynomialDriftVariation
import Proof.EndpointBoundaryCalculus
import Proof.FlatFullCoefficientOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory MvPolynomial
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility
open OAI.AnisotropicCalderon.GreenRadialTrace

/-- The explicit polynomial first variation lies in the genuine zero-boundary
    strong Dirichlet domain, using the constructive native trace kernel. -/
theorem driftFirstVariation_mem_strongDirichlet (k : ℕ) (d : Fin 3 → ℝ) (p : MvPolynomial I ℝ) :
    polynomialBallSobolev 2 (driftFirstVariation k d p) ∈ strongDirichletSubmodule 0 := by
  have hSphere : polynomialSphere (driftFirstVariation k d p) = 0 := by
    apply ContinuousMap.ext
    intro z
    change eval (fun i => z.val i) (driftFirstVariation k d p) = 0
    exact eval_driftFirstVariation_eq_zero k d p _ (unitSphere_sum_sq z)
  have hTrace : strongValueTraceL fixedUnitBallValueTrace 0
      (polynomialBallSobolev 2 (driftFirstVariation k d p)) = 0 := by
    rw [strongValueTraceL_polynomialBallSobolev]
    change (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere (driftFirstVariation k d p)) = 0
    rw [hSphere,map_zero]
  apply (mem_strongDirichletSubmodule 0 _).mpr
  exact (fixedUnitBallValueTrace_kernel _).mp hTrace

def polynomialDriftDirichlet (k : ℕ) (d : Fin 3 → ℝ) (p : MvPolynomial I ℝ) : StrongDirichletSpace 0 :=
  ⟨polynomialBallSobolev 2 (driftFirstVariation k d p),driftFirstVariation_mem_strongDirichlet k d p⟩

lemma laplacian_driftFirstVariation_eq {k : ℕ} (p : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) (d : Fin 3 → ℝ) :
    laplacian (driftFirstVariation k d p) = -driftDerivative d p := by
  rw [driftFirstVariation,laplacian_radialFirstVariation (driftDerivative_isHomogeneous hp d)
    (laplacian_driftDerivative d p hΔ) (ne_of_gt (radiusSq_laplacian_coefficient_pos (k-1)))]

/-- The explicit first variation has exactly the native flat Dirichlet forcing. -/
theorem flat_strong_polynomialDriftDirichlet (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1)
    (c : ℝ) {k : ℕ} (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0)
    (d : Fin 3 → ℝ) :
    strongDirichletOperator fixedSobolevCalculus 0 (c • F0) (polynomialDriftDirichlet k d p) =
      c • polynomialBallSobolev 0 (driftDerivative d p) := by
  have hOp := fullCoefficientOperatorL_comp_subtype fixedSobolevCalculus 0 (c • F0)
  rw [← hOp]
  change fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)
    (polynomialBallSobolev 2 (driftFirstVariation k d p)) = _
  rw [map_smul,ContinuousLinearMap.smul_apply,fullCoefficientOperator_flat_eq fixedSobolevCalculus F0 hF0]
  change c • (-(nativeEuclideanLaplacianL fixedSobolevCalculus
    (polynomialBallSobolev 2 (driftFirstVariation k d p)))) = _
  rw [nativeEuclideanLaplacianL_polynomialBallSobolev,laplacian_driftFirstVariation_eq p hp hΔ d]
  change c • (-(polynomialBallSobolevLinearMap 0 (-driftDerivative d p))) = _
  rw [map_neg,neg_neg]
  rfl

/-- Canonical inverse evaluation for the affine first variation, with the
    positive scalar center carried explicitly. -/
theorem flat_inverse_polynomial_drift (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1)
    (c : ℝ) (hc : c ≠ 0)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    {k : ℕ} (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0)
    (d : Fin 3 → ℝ) :
    (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse
      (polynomialBallSobolev 0 (driftDerivative d p)) = c⁻¹ • polynomialDriftDirichlet k d p := by
  have hApply : strongDirichletOperator fixedSobolevCalculus 0 (c • F0)
      (c⁻¹ • polynomialDriftDirichlet k d p) = polynomialBallSobolev 0 (driftDerivative d p) := by
    rw [map_smul,flat_strong_polynomialDriftDirichlet F0 hF0 c p hp hΔ d,smul_smul,inv_mul_cancel₀ hc,one_smul]
  rw [← hApply,hInv.inverse_apply_self]

end ShrinkingSpheres
