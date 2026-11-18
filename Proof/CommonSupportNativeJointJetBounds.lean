import Proof.ParameterSpatialJetBounds
import Proof.CommonSupportPoissonHigherJets
import Proof.MatrixFieldJetNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma norm_iteratedFDeriv_parameter_spatial_matrix_entry_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) (x : X) (n k : ℕ) (i j : I) :
    ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k (fun z => a (t,z) i j) x) p‖ ≤
      ‖iteratedFDeriv ℝ (n+k) a (p,x)‖ := by
  have hL : ‖matrixEntryL i j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    change ‖A i j‖ ≤ 1*‖A‖
    simpa only [one_mul] using Matrix.norm_entry_le_entrywise_sup_norm A (i:=i) (j:=j)
  have hA := (matrixEntryL i j).contDiff.comp ha
  have hMixed := norm_iteratedFDeriv_parameter_spatial_jet_le ((matrixEntryL i j) ∘ a) hA p x n k
  exact hMixed.trans ((norm_iteratedFDeriv_clm_comp_le (matrixEntryL i j) a (p,x) ha.contDiffAt (n+k)).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _)))

/-- Checked joint-coefficient caller for the SAME actual strong/weak inverses,
    Poisson lifts and weak conormal response. All coefficient bounds are local
    on the unit ball; a global compact representative supplies smoothness only. -/
theorem commonSupport_native_poisson_jets_of_joint_bound
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (N : ℕ) (CI q : ℝ) (hCI : 0 ≤ CI) (hq : 0 ≤ q)
    (hStrong : (strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha K hK hz p)).IsInvertible)
    (hStrongNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha K hK hz p)).inverse‖ ≤ CI)
    (hWeak : (commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (hWeakNorm : ‖(commonSupportZeroWeakEnergy a ha p).inverse‖ ≤ CI)
    (hJoint : ∀ l : ℕ,l ≤ N+1 → ∀ x ∈ (ballOpens:Set X),‖iteratedFDeriv ℝ l a (p,x)‖ ≤ q) :
    let F := commonSupportMatrixFamily 2 a ha K hK hz
    ∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (fun t => (strongDirichletOperator fixedSobolevCalculus 0 (F t)).inverse) p‖ ≤
        inverseFamilyJetBudget N CI (2*strongC1OperatorBudget fixedSobolevCalculus*q) ∧
      ‖iteratedFDeriv ℝ n (fun t => (commonSupportZeroWeakEnergy a ha t).inverse) p‖ ≤
        inverseFamilyJetBudget N CI (weakFullDerivativeBudget*q) ∧
      ‖iteratedFDeriv ℝ n (fun t => strongPoissonL (F t)) p‖ ≤ strongPoissonJetBudget N CI q ∧
      ‖iteratedFDeriv ℝ n (commonSupportWeakHalfLift a ha) p‖ ≤ weakPoissonJetBudget N CI q ∧
      ‖iteratedFDeriv ℝ n (commonSupportWeakConormalEndpoint a ha) p‖ ≤ weakConormalJetBudget N CI q := by
  have hMixed (l : ℕ) (hl : l ≤ N) (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q :=
    (norm_iteratedFDeriv_parameter_spatial_matrix_entry_le a ha p x l k.val i j).trans
      (hJoint (l+k.val) (by omega) x hx)
  have hValue (l : ℕ) (hl : l ≤ N) (i j : I) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q :=
    hMixed l hl i j ⟨0,by omega⟩ x hx
  intro F n hn
  have hSB := strongC1OperatorBudget_nonneg fixedSobolevCalculus
  have hWB := weakFullDerivativeBudget_nonneg
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact norm_iteratedFDeriv_inverse_family_le_of_isInvertible (P:=P)
      (E:=StrongDirichletSpace 0) (F:=BallSobolev 0)
      (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)) p hStrong
      (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha K hK hz).contDiffAt
      N CI (2*strongC1OperatorBudget fixedSobolevCalculus*q) hCI (by positivity) hStrongNorm
      (fun l _ hl => norm_iteratedFDeriv_commonSupport_strongOperator_zero_le fixedSobolevCalculus
        a ha K hK hz p l q hq (hMixed l hl)) n hn
  · exact norm_iteratedFDeriv_inverse_family_le_of_isInvertible (P:=P)
      (E:=BallH1Zero) (F:=StrongDual ℝ BallH1Zero)
      (commonSupportZeroWeakEnergy a ha) p hWeak
      (contDiff_commonSupportZeroWeakEnergy a ha K hK hz).contDiffAt
      N CI (weakFullDerivativeBudget*q) hCI (by positivity) hWeakNorm
      (fun l _ hl => norm_iteratedFDeriv_commonSupportZeroWeakEnergy_le a ha K hK hz p l q hq (hValue l hl)) n hn
  · exact norm_iteratedFDeriv_commonSupport_strongPoissonL_le a ha K hK hz p N CI q hCI hq hStrong hStrongNorm hMixed n hn
  · exact norm_iteratedFDeriv_commonSupportWeakHalfLift_le a ha K hK hz p N CI q hCI hq hWeak hWeakNorm hValue n hn
  · exact norm_iteratedFDeriv_commonSupportWeakConormalEndpoint_le a ha K hK hz p N CI q hCI hq hWeak hWeakNorm hValue n hn

end ShrinkingSpheres
