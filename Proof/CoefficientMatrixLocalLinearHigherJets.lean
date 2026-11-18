import Proof.ClosedBoundaryMatrixMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology BoundedContinuousFunction Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def coefficientMatrixLocalLinearExtensionL (L : SmoothCoefficientMatrix 2 →L[ℝ] V) :
    ClosedCoefficientMatrix 2 →L[ℝ] V := L.extend (smoothCoefficientMatrixClosureInclusionL 2)

theorem coefficientMatrixLocalLinearExtension_eq_on_smooth
    (L : SmoothCoefficientMatrix 2 →L[ℝ] V) (F : SmoothCoefficientMatrix 2) :
    coefficientMatrixLocalLinearExtensionL L (smoothCoefficientMatrixClosureInclusionL 2 F) = L F :=
  L.extend_eq (denseRange_smoothCoefficientMatrixClosureInclusionL 2)
    (isometry_smoothCoefficientMatrixClosureInclusionL 2).isUniformInducing F

theorem norm_coefficientMatrixLocalLinearExtension_local_le
    (L : SmoothCoefficientMatrix 2 →L[ℝ] V) (A : ℝ) (hA : 0 ≤ A)
    (hLocal : ∀ (F : SmoothCoefficientMatrix 2) (q : ℝ),0 ≤ q →
      (∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) x| ≤ q) →
      (∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) → ‖L F‖ ≤ A*q) (F : ClosedCoefficientMatrix 2) :
    ‖coefficientMatrixLocalLinearExtensionL L F‖ ≤
      A*closedCoefficientMatrixLocalC1Budget F := by
  have hDense : ∀ G ∈ range (smoothCoefficientMatrixClosureInclusionL 2),
      ‖coefficientMatrixLocalLinearExtensionL L G‖ ≤
        A*closedCoefficientMatrixLocalC1Budget G := by
    rintro _ ⟨G,rfl⟩
    rw [coefficientMatrixLocalLinearExtension_eq_on_smooth]
    let F := smoothCoefficientMatrixClosureInclusionL 2 G
    apply hLocal G (closedCoefficientMatrixLocalC1Budget F)
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

theorem norm_coefficientMatrixLocalLinearExtension_le_of_local_jets
    (L : SmoothCoefficientMatrix 2 →L[ℝ] V) (A : ℝ) (hA : 0 ≤ A)
    (hLocal : ∀ (F : SmoothCoefficientMatrix 2) (q : ℝ),0 ≤ q →
      (∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) x| ≤ q) →
      (∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) → ‖L F‖ ≤ A*q)
    (F : ClosedCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ l : Fin 2,∀ x : ballOpens,‖(F i j).val ⟨l.val,by omega⟩ x‖ ≤ q) :
    ‖coefficientMatrixLocalLinearExtensionL L F‖ ≤ (18*A)*q := by
  exact (norm_coefficientMatrixLocalLinearExtension_local_le L A hA hLocal F).trans
    ((mul_le_mul_of_nonneg_left (closedCoefficientMatrixLocalC1Budget_le F q hq hJets) (by positivity)).trans_eq (by ring))

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- All finite parameter derivatives of the true completed normal/tangent
    multipliers require only the same local coefficient value and C1 jets. -/
theorem norm_iteratedFDeriv_coefficientMatrixLocalLinearExtension_le
    (L : SmoothCoefficientMatrix 2 →L[ℝ] V) (A : ℝ) (hA : 0 ≤ A)
    (hLocal : ∀ (F : SmoothCoefficientMatrix 2) (q : ℝ),0 ≤ q →
      (∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) x| ≤ q) →
      (∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) → ‖L F‖ ≤ A*q)
    (F : P → ClosedCoefficientMatrix 2) (p : P) (hF : ContDiffAt ℝ ∞ F p)
    (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ l : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => (F t i j).val ⟨l.val,by omega⟩ x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => coefficientMatrixLocalLinearExtensionL L (F t)) p‖ ≤
      (18*A)*q := by
  change ‖iteratedFDeriv ℝ n (coefficientMatrixLocalLinearExtensionL L ∘ F) p‖ ≤ _
  rw [(coefficientMatrixLocalLinearExtensionL L).iteratedFDeriv_comp_left hF (i:=n) (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  change ‖coefficientMatrixLocalLinearExtensionL L (iteratedFDeriv ℝ n F p v)‖ ≤ _
  have hEvalLocal (i j : I) (l : Fin 2) (x : ballOpens) :
      ‖(iteratedFDeriv ℝ n F p v i j).val ⟨l.val,by omega⟩ x‖ ≤ q*∏ m,‖v m‖ := by
    rw [iteratedFDeriv_closedCoefficientMatrix_jet_eval F p hF]
    exact ((iteratedFDeriv ℝ n (fun t => (F t i j).val ⟨l.val,by omega⟩ x) p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hJets i j l x x.property) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact (norm_coefficientMatrixLocalLinearExtension_le_of_local_jets L A hA hLocal _ (q*∏ m,‖v m‖) (by positivity) hEvalLocal).trans_eq (by ring)

end ShrinkingSpheres
