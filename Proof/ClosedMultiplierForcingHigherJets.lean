import Proof.ClosedLocalMultiplierForcing
import Proof.CommonSupportMultiplierHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient BoundedContinuousFunction Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma closedCoefficientMatrixLocalC1Budget_le (F : ClosedCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x : ballOpens,‖(F i j).val ⟨k.val,by omega⟩ x‖ ≤ q) :
    closedCoefficientMatrixLocalC1Budget F ≤ 18*q := by
  have hLocal (i j : I) (k : Fin 2) : ‖closedCoefficientLocalJetL 2 ⟨k.val,by omega⟩ (F i j)‖ ≤ q :=
    (BoundedContinuousFunction.norm_le hq).mpr (hJets i j k)
  calc
    _ ≤ ∑ i : I,∑ j : I,∑ k : Fin 2,q := Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hLocal i j k)))
    _ = _ := by simp [I];ring

theorem norm_closedNativeBulkMultiplierForcing_le_of_local_jets
    (F : ClosedCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) (q B : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x : ballOpens,‖(F i j).val ⟨k.val,by omega⟩ x‖ ≤ q)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B) :
    ‖closedNativeBulkMultiplierForcingL F Q‖ ≤ (270*nativeMultiplierForcingGradientBudget*B)*q := by
  have hG := nativeMultiplierForcingGradientBudget_nonneg
  exact (norm_closedNativeBulkMultiplierForcing_local_le F Q B hB hQ1 hQ2).trans
    ((mul_le_mul_of_nonneg_left (closedCoefficientMatrixLocalC1Budget_le F q hq hJets)
      (by positivity)).trans_eq (by ring))

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def closedCoefficientMatrixEntryL (r : ℕ) (i j : I) :
    ClosedCoefficientMatrix r →L[ℝ] ClosedCoefficientJets r :=
  (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : I => ClosedCoefficientJets r) j).comp
    (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : I => I → ClosedCoefficientJets r) i)

lemma iteratedFDeriv_closedCoefficientMatrix_jet_eval
    (F : P → ClosedCoefficientMatrix 2) (p : P) (hF : ContDiffAt ℝ ∞ F p)
    (n : ℕ) (v : Fin n → P) (i j : I) (k : Fin 2) (x : X) :
    (iteratedFDeriv ℝ n F p v i j).val ⟨k.val,by omega⟩ x =
      iteratedFDeriv ℝ n (fun t => (F t i j).val ⟨k.val,by omega⟩ x) p v := by
  let ev := (closedCoefficientJetEvaluationL 2 ⟨k.val,by omega⟩ x).comp
    (closedCoefficientMatrixEntryL 2 i j)
  have h := ev.iteratedFDeriv_comp_left hF (i:=n) (by simp)
  change _ = (iteratedFDeriv ℝ n (ev ∘ F) p) v
  exact (congrArg (fun A => A v) h).symm

/-- Only local coefficient value and first spatial jets enter every parameter
    derivative of the actual multiplier forcing. The multiplier is fixed. -/
theorem norm_iteratedFDeriv_closedNativeBulkMultiplierForcing_le
    (F : P → ClosedCoefficientMatrix 2) (p : P) (hF : ContDiffAt ℝ ∞ F p)
    (Q : SmoothCoefficientJets 3) (n : ℕ) (q B : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => (F t i j).val ⟨k.val,by omega⟩ x) p‖ ≤ q)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun t => closedNativeBulkMultiplierForcingL (F t) Q) p‖ ≤
      (270*nativeMultiplierForcingGradientBudget*B)*q := by
  have hG := nativeMultiplierForcingGradientBudget_nonneg
  let ev := (ContinuousLinearMap.apply ℝ (BallH1 →L[ℝ] BallSobolev 0) Q).comp
    closedNativeBulkMultiplierForcingL
  have h := ev.iteratedFDeriv_comp_left hF (i:=n) (by simp)
  change ‖iteratedFDeriv ℝ n (ev ∘ F) p‖ ≤ _
  rw [h]
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  change ‖closedNativeBulkMultiplierForcingL (iteratedFDeriv ℝ n F p v) Q‖ ≤ _
  have hLocal (i j : I) (k : Fin 2) (x : ballOpens) :
      ‖(iteratedFDeriv ℝ n F p v i j).val ⟨k.val,by omega⟩ x‖ ≤ q*∏ l,‖v l‖ := by
    rw [iteratedFDeriv_closedCoefficientMatrix_jet_eval F p hF]
    exact ((iteratedFDeriv ℝ n (fun t => (F t i j).val ⟨k.val,by omega⟩ x) p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hJets i j k x x.property) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  exact (norm_closedNativeBulkMultiplierForcing_le_of_local_jets _ Q (q*∏ l,‖v l‖) B
    (by positivity) hB hLocal hQ1 hQ2).trans_eq (by ring)

variable [FiniteDimensional ℝ P]

theorem norm_iteratedFDeriv_commonSupport_nativeBulkMultiplierForcing_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p : P) (Q : SmoothCoefficientJets 3)
    (n : ℕ) (q B : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus
      (commonSupportMatrixFamily 2 a ha S hS hz t) (fun _ => 0) Q) p‖ ≤
      (270*nativeMultiplierForcingGradientBudget*B)*q := by
  let F := commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz
  have hEq : (fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus
      (commonSupportMatrixFamily 2 a ha S hS hz t) (fun _ => 0) Q) =
      (fun t => closedNativeBulkMultiplierForcingL (F t) Q) := by
    funext t
    exact (closedNativeBulkMultiplierForcingL_eq_on_smooth _ Q).symm
  rw [hEq]
  apply norm_iteratedFDeriv_closedNativeBulkMultiplierForcing_le F p
    (contDiff_commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz).contDiffAt Q n q B hq hB _ hQ1 hQ2
  exact hJets

end ShrinkingSpheres
