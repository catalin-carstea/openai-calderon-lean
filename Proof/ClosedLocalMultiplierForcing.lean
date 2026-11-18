import Proof.ClosedCoefficientMatrixInclusion
import Proof.NativeMultiplierForcingBilinear
import Proof.ClosedLocalCoefficientJets
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient BoundedContinuousFunction Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

local instance : CompleteSpace (BallSobolev 0) := by
  change CompleteSpace (Lp ℝ 2 ((volume:Measure X).restrict ballOpens))
  infer_instance

local instance : CompleteSpace (BallH1 →L[ℝ] BallSobolev 0) := by infer_instance
local instance : CompleteSpace (SmoothCoefficientJets 3 →L[ℝ] (BallH1 →L[ℝ] BallSobolev 0)) := by infer_instance

def closedNativeBulkMultiplierForcingL : ClosedCoefficientMatrix 2 →L[ℝ]
    SmoothCoefficientJets 3 →L[ℝ] (BallH1 →L[ℝ] BallSobolev 0) :=
  nativeBulkMultiplierForcingBilinearL.extend (smoothCoefficientMatrixClosureInclusionL 2)

theorem closedNativeBulkMultiplierForcingL_eq_on_smooth
    (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) :
    closedNativeBulkMultiplierForcingL (smoothCoefficientMatrixClosureInclusionL 2 F) Q =
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q := by
  have h := nativeBulkMultiplierForcingBilinearL.extend_eq
    (denseRange_smoothCoefficientMatrixClosureInclusionL 2)
    (isometry_smoothCoefficientMatrixClosureInclusionL 2).isUniformInducing F
  exact congrArg (fun L => L Q) h

def closedCoefficientMatrixLocalC1Budget (F : ClosedCoefficientMatrix 2) : ℝ :=
  ∑ i : I,∑ j : I,∑ k : Fin 2,‖closedCoefficientLocalJetL 2 ⟨k.val,by omega⟩ (F i j)‖

lemma closedCoefficientMatrixLocalC1Budget_nonneg (F : ClosedCoefficientMatrix 2) :
    0 ≤ closedCoefficientMatrixLocalC1Budget F := by
  unfold closedCoefficientMatrixLocalC1Budget
  positivity

lemma closedCoefficientLocalJet_norm_le_matrixBudget (F : ClosedCoefficientMatrix 2) (i j : I) (k : Fin 2) :
    ‖closedCoefficientLocalJetL 2 ⟨k.val,by omega⟩ (F i j)‖ ≤ closedCoefficientMatrixLocalC1Budget F := by
  unfold closedCoefficientMatrixLocalC1Budget
  calc
    _ ≤ ∑ l : Fin 2,‖closedCoefficientLocalJetL 2 ⟨l.val,by omega⟩ (F i j)‖ :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ b : I,∑ l : Fin 2,‖closedCoefficientLocalJetL 2 ⟨l.val,by omega⟩ (F i b)‖ :=
      Finset.single_le_sum (f:=fun b : I => ∑ l : Fin 2,
        ‖closedCoefficientLocalJetL 2 ⟨l.val,by omega⟩ (F i b)‖)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f:=fun a : I => ∑ b : I,∑ l : Fin 2,
      ‖closedCoefficientLocalJetL 2 ⟨l.val,by omega⟩ (F a b)‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))) (Finset.mem_univ i)

/-- The completed coefficient interface retains the sharp locality of the
    supplied forcing estimate. Only local coefficient C1 jets and local first
    two multiplier jets enter, even though extension uses a global norm. -/
theorem norm_closedNativeBulkMultiplierForcing_local_le
    (F : ClosedCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) (B : ℝ) (hB : 0 ≤ B)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B) :
    ‖closedNativeBulkMultiplierForcingL F Q‖ ≤
      (15*nativeMultiplierForcingGradientBudget*B)*closedCoefficientMatrixLocalC1Budget F := by
  have hDense : ∀ G ∈ range (smoothCoefficientMatrixClosureInclusionL 2),
      ‖closedNativeBulkMultiplierForcingL G Q‖ ≤
        (15*nativeMultiplierForcingGradientBudget*B)*closedCoefficientMatrixLocalC1Budget G := by
    rintro _ ⟨G,rfl⟩
    rw [closedNativeBulkMultiplierForcingL_eq_on_smooth]
    let F := smoothCoefficientMatrixClosureInclusionL 2 G
    apply norm_nativeBulkMultiplierForcing_local_C1 G Q (closedCoefficientMatrixLocalC1Budget F) B
      (closedCoefficientMatrixLocalC1Budget_nonneg F) hB
    · intro i j x hx
      have h := (closedCoefficientLocalJetL 2 ⟨0,by omega⟩ (F i j)).norm_coe_le_norm ⟨x,hx⟩
      change ‖(G i j).val ⟨0,by omega⟩ x‖ ≤ _ at h
      rw [coefficientJet_eq_iteratedFDeriv,norm_iteratedFDeriv_zero] at h
      exact h.trans (closedCoefficientLocalJet_norm_le_matrixBudget F i j ⟨0,by omega⟩)
    · intro i j x hx
      rw [TauCeti.norm_gradient_eq_norm_fderiv]
      have h := (closedCoefficientLocalJetL 2 ⟨1,by omega⟩ (F i j)).norm_coe_le_norm ⟨x,hx⟩
      change ‖(G i j).val ⟨1,by omega⟩ x‖ ≤ _ at h
      rw [coefficientJet_eq_iteratedFDeriv,norm_iteratedFDeriv_one] at h
      exact h.trans (closedCoefficientLocalJet_norm_le_matrixBudget F i j ⟨1,by omega⟩)
    · exact hQ1
    · exact hQ2
  exact (denseRange_smoothCoefficientMatrixClosureInclusionL 2).induction hDense
    (isClosed_le (by fun_prop) (by unfold closedCoefficientMatrixLocalC1Budget;fun_prop)) F

end ShrinkingSpheres
