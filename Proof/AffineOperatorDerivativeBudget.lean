import Proof.LocalCoefficientOperatorCongruence
import Proof.PoissonTaylorDerivative
import Proof.CommonSupportPoissonRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local irreducible] strongCoefficientOperatorL fullCoefficientOperatorL

/-- A genuine shared affine coefficient identity passes its quadratic derivative
    budget to the full operator remainder and its radius-linear budget to the
    actual principal strong operator. -/
theorem coefficientOperators_affine_derivative_budget
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F F1 R : P → SmoothCoefficientMatrix 2) (F0 : SmoothCoefficientMatrix 2)
    (x : P) (U : Set P) (hU : IsOpen U) (hx : x ∈ U) (r C1 CR : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC1 : 0 ≤ C1) (hCR : 0 ≤ CR)
    (hField : ∀ p ∈ U,∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (R p) z =
      coefficientMatrixField 2 (F p) z-coefficientMatrixField 2 F0 z-r • coefficientMatrixField 2 (F1 p) z)
    (hD1 : DifferentiableAt ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F1 p)) x)
    (hDR : DifferentiableAt ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (R p)) x)
    (hN1 : ‖fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F1 p)) x‖ ≤ C1)
    (hNR : ‖fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (R p)) x‖ ≤ CR*r^2)
    (hNFull : ‖fderiv ℝ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (R p)) x‖ ≤ CR*r^2) :
    ‖fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F p)) x‖ ≤ (C1+CR)*r ∧
      ‖fderiv ℝ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)-
        fullCoefficientOperatorL fixedSobolevCalculus 0 F0-
        r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 p)) x‖ ≤ CR*r^2 := by
  have hS : (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F p)) =ᶠ[𝓝 x]
      (fun p => strongDirichletOperator fixedSobolevCalculus 0 F0+
        r • strongDirichletOperator fixedSobolevCalculus 0 (F1 p)+strongDirichletOperator fixedSobolevCalculus 0 (R p)) := by
    filter_upwards [hU.mem_nhds hx] with p hp
    have h := (coefficientOperators_affine_identity fixedSobolevCalculus (F p) F0 (F1 p) (R p) r (hField p hp)).1
    rw [← h]
    abel
  have hF : (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)-
      fullCoefficientOperatorL fixedSobolevCalculus 0 F0-r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 p)) =ᶠ[𝓝 x]
      (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (R p)) := by
    filter_upwards [hU.mem_nhds hx] with p hp
    exact (coefficientOperators_affine_identity fixedSobolevCalculus (F p) F0 (F1 p) (R p) r (hField p hp)).2
  refine ⟨?_,?_⟩
  rotate_left
  · rw [hF.fderiv_eq]
    exact hNFull
  rw [hS.fderiv_eq]
  have hD := (((hasFDerivAt_const (𝕜:=ℝ)
    (strongDirichletOperator fixedSobolevCalculus 0 F0) x).add
      (hD1.hasFDerivAt.const_smul r)).add hDR.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 F0+
      r • strongDirichletOperator fixedSobolevCalculus 0 (F1 p)+strongDirichletOperator fixedSobolevCalculus 0 (R p)) x =
    0+r • fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F1 p)) x+
      fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (R p)) x at hD
  rw [hD]
  simp only [zero_add]
  calc
    _ ≤ ‖r • fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F1 p)) x‖+
        ‖fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (R p)) x‖ := norm_add_le _ _
    _ ≤ r*C1+CR*r^2 := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr];gcongr
    _ ≤ (C1+CR)*r := by nlinarith [mul_le_mul_of_nonneg_left hr1 hr]

end ShrinkingSpheres
