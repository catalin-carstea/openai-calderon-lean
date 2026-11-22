module

public import Proof.CalderonN.FixedBallSourceEnergy
public import Mathlib.Analysis.Matrix.Normed
import Proof.CalderonN.CompactEllipticity
import Mathlib.Tactic

public section

/- Uniform fixed-ball ellipticity from the 3D Theorem 3.1 release. -/
noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonN
variable {n : ℕ} [NeZero n]

private theorem exists_fixedBall_coefficient_upper_bound (A : (X n) → (Mat n)) (hA : Continuous A) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ closedBall (0 : (X n)) 1,
      ∀ η ξ : (X n), |dotProduct (η : I n → ℝ) (Matrix.mulVec (A x) (ξ : I n → ℝ))| ≤ M * ‖η‖ * ‖ξ‖ := by
  have hcont : Continuous fun x => ‖TauCeti.PDE.matrixBilinearForm (A x)‖ :=
    (continuous_norm (E := (X n) →L[ℝ] (X n) →L[ℝ] ℝ)).comp
      (TauCeti.PDE.continuous_matrixBilinearForm.comp hA)
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : (X n)) 1).bddAbove_image hcont.continuousOn
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun x hx η ξ => ?_⟩
  have hb : ‖TauCeti.PDE.matrixBilinearForm (A x)‖ ≤ max M 1 :=
    (hM (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  calc
    |dotProduct (η : I n → ℝ) (Matrix.mulVec (A x) (ξ : I n → ℝ))| = ‖TauCeti.PDE.matrixBilinearForm (A x) η ξ‖ := by
      rw [TauCeti.PDE.matrixBilinearForm_apply,Real.norm_eq_abs]
    _ ≤ ‖TauCeti.PDE.matrixBilinearForm (A x)‖ * ‖η‖ * ‖ξ‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ max M 1 * ‖η‖ * ‖ξ‖ := by gcongr

private theorem exists_fixedBall_coefficient_lower_bound (A : (X n) → (Mat n)) (hA : Continuous A)
    (hPos : ∀ x ∈ closedBall (0 : (X n)) 1, (A x).PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ closedBall (0 : (X n)) 1,
      ∀ ξ : (X n), lam * ‖ξ‖ ^ 2 ≤ (A x).toQuadraticForm' ξ := by
  obtain ⟨lo, hlo, hbound⟩ := Elliptic.lower_ellipticity_on_compact
    (a := fun i j x => A x i j)
    (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hA))
    (isCompact_closedBall (0 : X n) 1) hPos
  refine ⟨lo, hlo, fun x hx ξ => ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq, Matrix.toQuadraticForm'_apply]
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using
    hbound x hx (ξ : I n → ℝ)

theorem exists_uniformEllipticOn_fixedBall (A : (X n) → (Mat n)) (hA : Continuous A)
    (hPos : ∀ x ∈ closedBall (0 : (X n)) 1, (A x).PosDef) :
    ∃ lam Λ : ℝ, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) A lam Λ := by
  obtain ⟨lam,hlam,hlower⟩ := exists_fixedBall_coefficient_lower_bound A hA hPos
  obtain ⟨M,_,hupper⟩ := exists_fixedBall_coefficient_upper_bound A hA
  refine ⟨lam,max M lam,hlam,le_max_right _ _,fun x hx => ?_⟩
  have hx' := ball_subset_closedBall hx
  refine ⟨hlower x hx',fun η ξ => ?_⟩
  exact (hupper x hx' η ξ).trans (by gcongr; exact le_max_left _ _)

end CalderonN
