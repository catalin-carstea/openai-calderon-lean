import Proof.SharpStrongOperator
import Proof.UniformStrongDirichletInverse
import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

lemma coefficientMatrixField_smul (r : ℕ) (c : ℝ) (F : SmoothCoefficientMatrix r) (x : X) :
    coefficientMatrixField r (c • F) x = c • coefficientMatrixField r F x := by
  ext i j
  change coefficientValue r (c • F i j) x = c*coefficientValue r (F i j) x
  rw [coefficientValue_smul]
  rfl

/-- A common strong inverse neighborhood of the entire compact interval of
    positive scalar Euclidean coefficients, controlled only in local C1. -/
theorem exists_uniform_strongC1_neighborhood (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ F0 : SmoothCoefficientMatrix 2,
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∃ δ C : ℝ,0 < δ ∧ 0 ≤ C ∧ ∀ c ∈ Icc lo hi,
      ∀ (F : SmoothCoefficientMatrix 2) (lam Lam : ℝ),
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X) (coefficientMatrixField 2 F) lam Lam →
      (∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0) i j) x| ≤ δ) →
      (∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0) i j)) x‖ ≤ δ) →
      ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C := by
  obtain ⟨F0,hF0⟩ := exists_flatCoefficientMatrix 2
  have hField (c : ℝ) (x : X) (hx : x ∈ (ballOpens : Set X)) :
      coefficientMatrixField 2 (c • F0) x = c • (1:Mat) := by
    rw [coefficientMatrixField_smul,hF0 x (unitBall_subset_closedBall_two hx)]
  have hUE (c : ℝ) (hc : c ∈ Icc lo hi) :
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X) (coefficientMatrixField 2 (c • F0)) c c := by
    have hCpos : 0 < c := hlo.trans_le hc.1
    have hh := TauCeti.PDE.uniformlyEllipticOn_smul_one (n:=I) (ballOpens : Set X)
      (fun _ : X => c) hCpos le_rfl (fun _ _ => ⟨le_rfl,le_rfl⟩)
    refine ⟨hCpos,le_rfl,?_⟩
    intro x hx
    rw [hField c x hx]
    exact hh.2.2 hx
  obtain ⟨C0,hC0,hCenter⟩ := exists_uniform_strongDirichletInverseFamily_bound
    fixedSobolevCalculus fixedDirichletRegularity 0 (fun c : ℝ => c • F0) (Icc lo hi) isCompact_Icc
    (ContinuousLinearMap.toSpanSingleton ℝ F0).continuous.continuousOn (fun c => c) (fun c => c) hUE
  let B := C0+1
  let S := strongC1OperatorBudget fixedSobolevCalculus
  let δ := (2*(B+1)*(S+1))⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  have hS : 0 ≤ S := strongC1OperatorBudget_nonneg fixedSobolevCalculus
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨F0,hF0,δ,2*B,hδ,by positivity,?_⟩
  intro c hc F lam Lam hEll hVal hDeriv
  let A := strongDirichletOperator fixedSobolevCalculus 0 F
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 (c • F0)
  have hA : A.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 F hEll
  have hA0 : A0.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 (c • F0) (hUE c hc)
  have hDiff : ‖A-A0‖ ≤ S*δ := norm_strongDirichletOperator_zero_sub_le
    fixedSobolevCalculus F (c • F0) δ hδ.le hVal hDeriv
  apply inverse_norm_le_twice_of_half_perturbation A A0 hA hA0 B hB.le
    ((hCenter c hc).trans (by dsimp [B]; linarith))
  have hOne : 2*(B+1)*(S+1)*δ = 1 := mul_inv_cancel₀ (by positivity)
  have hCompare : 2*B*S ≤ 2*(B+1)*(S+1) := by nlinarith only [hB.le,hS]
  have hBound := mul_le_mul_of_nonneg_right hCompare hδ.le
  have hBD := mul_le_mul_of_nonneg_left hDiff hB.le
  nlinarith only [hOne,hBound,hBD]

end ShrinkingSpheres
