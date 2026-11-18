import Proof.BoundaryMatrixMultiplierLinear
import Proof.ClosedMultiplierForcingHigherJets
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology BoundedContinuousFunction Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def closedBoundaryMatrixMultiplierL (k : Option I) : ClosedCoefficientMatrix 2 →L[ℝ]
    (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  (boundaryMatrixMultiplierL k).extend (smoothCoefficientMatrixClosureInclusionL 2)

theorem closedBoundaryMatrixMultiplierL_eq_on_smooth (k : Option I) (F : SmoothCoefficientMatrix 2) :
    closedBoundaryMatrixMultiplierL k (smoothCoefficientMatrixClosureInclusionL 2 F) =
      boundaryMatrixMultiplier k F := by
  exact (boundaryMatrixMultiplierL k).extend_eq
    (denseRange_smoothCoefficientMatrixClosureInclusionL 2)
    (isometry_smoothCoefficientMatrixClosureInclusionL 2).isUniformInducing F

theorem norm_closedBoundaryMatrixMultiplier_local_le (k : Option I) (F : ClosedCoefficientMatrix 2) :
    ‖closedBoundaryMatrixMultiplierL k F‖ ≤
      (78*boundaryHalfMultiplierBudget)*closedCoefficientMatrixLocalC1Budget F := by
  have hDense : ∀ G ∈ range (smoothCoefficientMatrixClosureInclusionL 2),
      ‖closedBoundaryMatrixMultiplierL k G‖ ≤
        (78*boundaryHalfMultiplierBudget)*closedCoefficientMatrixLocalC1Budget G := by
    rintro _ ⟨G,rfl⟩
    rw [closedBoundaryMatrixMultiplierL_eq_on_smooth]
    let F := smoothCoefficientMatrixClosureInclusionL 2 G
    apply norm_boundaryMatrixMultiplier_local_C1 k G (closedCoefficientMatrixLocalC1Budget F)
      (closedCoefficientMatrixLocalC1Budget_nonneg F)
    · intro i j x hx
      have h := (closedCoefficientLocalJetL 2 ⟨0,by omega⟩ (F i j)).norm_coe_le_norm ⟨x,hx⟩
      change ‖(G i j).val ⟨0,by omega⟩ x‖ ≤ _ at h
      rw [coefficientJet_eq_iteratedFDeriv,norm_iteratedFDeriv_zero] at h
      exact h.trans (closedCoefficientLocalJet_norm_le_matrixBudget F i j ⟨0,by omega⟩)
    · intro i j x hx
      have h := (closedCoefficientLocalJetL 2 ⟨1,by omega⟩ (F i j)).norm_coe_le_norm ⟨x,hx⟩
      change ‖(G i j).val ⟨1,by omega⟩ x‖ ≤ _ at h
      rw [coefficientJet_eq_iteratedFDeriv,norm_iteratedFDeriv_one] at h
      exact h.trans (closedCoefficientLocalJet_norm_le_matrixBudget F i j ⟨1,by omega⟩)
  exact (denseRange_smoothCoefficientMatrixClosureInclusionL 2).induction hDense
    (isClosed_le (by fun_prop) (by unfold closedCoefficientMatrixLocalC1Budget;fun_prop)) F

theorem norm_closedBoundaryMatrixMultiplier_le_of_local_jets (k : Option I)
    (F : ClosedCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ l : Fin 2,∀ x : ballOpens,‖(F i j).val ⟨l.val,by omega⟩ x‖ ≤ q) :
    ‖closedBoundaryMatrixMultiplierL k F‖ ≤ (1404*boundaryHalfMultiplierBudget)*q := by
  have hB := boundaryHalfMultiplierBudget_nonneg
  exact (norm_closedBoundaryMatrixMultiplier_local_le k F).trans
    ((mul_le_mul_of_nonneg_left (closedCoefficientMatrixLocalC1Budget_le F q hq hJets) (by positivity)).trans_eq (by ring))

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- All finite parameter derivatives of the true completed normal/tangent
    multipliers require only the same local coefficient value and C1 jets. -/
theorem norm_iteratedFDeriv_closedBoundaryMatrixMultiplier_le (k : Option I)
    (F : P → ClosedCoefficientMatrix 2) (p : P) (hF : ContDiffAt ℝ ∞ F p)
    (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ l : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => (F t i j).val ⟨l.val,by omega⟩ x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => closedBoundaryMatrixMultiplierL k (F t)) p‖ ≤
      (1404*boundaryHalfMultiplierBudget)*q := by
  have hB := boundaryHalfMultiplierBudget_nonneg
  change ‖iteratedFDeriv ℝ n (closedBoundaryMatrixMultiplierL k ∘ F) p‖ ≤ _
  rw [(closedBoundaryMatrixMultiplierL k).iteratedFDeriv_comp_left hF (i:=n) (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  change ‖closedBoundaryMatrixMultiplierL k (iteratedFDeriv ℝ n F p v)‖ ≤ _
  have hLocal (i j : I) (l : Fin 2) (x : ballOpens) :
      ‖(iteratedFDeriv ℝ n F p v i j).val ⟨l.val,by omega⟩ x‖ ≤ q*∏ m,‖v m‖ := by
    rw [iteratedFDeriv_closedCoefficientMatrix_jet_eval F p hF]
    exact ((iteratedFDeriv ℝ n (fun t => (F t i j).val ⟨l.val,by omega⟩ x) p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hJets i j l x x.property) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact (norm_closedBoundaryMatrixMultiplier_le_of_local_jets k _ (q*∏ m,‖v m‖) (by positivity) hLocal).trans_eq (by ring)

end ShrinkingSpheres
