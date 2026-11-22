module

public import Proof.CalderonN.BallRegularity.Spaces
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! From Proof/Archive/(CoefficientJetSpace dim).lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxHeartbeats 1200000
noncomputable section
open Function
open scoped ContDiff
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

 
abbrev CoefficientJetSpace (dim : ℕ) (r : ℕ) :=
  (j : Fin (r + 1)) →
    BoundedContinuousFunction (X dim) (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => (X dim)) ℝ)

instance (priority := 2000) instNormedAddCommGroupCoefficientJetSpace (r : ℕ) :
    NormedAddCommGroup ((CoefficientJetSpace dim) r) := by
  letI : ∀ j : Fin (r + 1), NormedAddCommGroup
      (BoundedContinuousFunction (X dim)
        (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => (X dim)) ℝ)) := fun _ => inferInstance
  unfold CoefficientJetSpace
  infer_instance

instance (priority := 2000) instNormedSpaceCoefficientJetSpace (r : ℕ) :
    NormedSpace ℝ ((CoefficientJetSpace dim) r) := by
  letI : ∀ j : Fin (r + 1), NormedSpace ℝ
      (BoundedContinuousFunction (X dim)
        (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => (X dim)) ℝ)) := fun _ => inferInstance
  unfold CoefficientJetSpace
  infer_instance

instance instContinuousAddCoefficientJetFields (r : ℕ) :
    ∀ j : Fin (r + 1),
      ContinuousAdd (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => (X dim)) ℝ) :=
  fun _ => inferInstance

 
def smoothCoefficientJetSubmodule (dim : ℕ) (r : ℕ) : Submodule ℝ ((CoefficientJetSpace dim) r) where
  carrier := {F | ∃ phi : (X dim) → ℝ, ContDiff ℝ ∞ phi ∧ HasCompactSupport phi ∧
    ∀ (j : Fin (r + 1)) (x : (X dim)), F j x = iteratedFDeriv ℝ j.val phi x}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    intro j x
    simpa using (iteratedFDeriv_const_smul_apply (a := (0 : ℝ))
      (show ContDiffAt ℝ j.val (0 : (X dim) → ℝ) x from contDiff_const.contDiffAt)).symm
  add_mem' := by
    rintro F G ⟨phi, hp, hpc, hF⟩ ⟨psi, hq, hqc, hG⟩
    refine ⟨phi + psi, hp.add hq, hpc.add hqc, ?_⟩
    intro j x
    change F j x + G j x = iteratedFDeriv ℝ j.val (phi + psi) x
    rw [hF, hG]
    exact (iteratedFDeriv_add_apply
      ((hp.of_le (by simp)).contDiffAt) ((hq.of_le (by simp)).contDiffAt)).symm
  smul_mem' := by
    rintro c F ⟨phi, hp, hpc, hF⟩
    refine ⟨c • phi, contDiff_const.smul hp, hpc.smul_left, ?_⟩
    intro j x
    change c • F j x = iteratedFDeriv ℝ j.val (c • phi) x
    rw [hF]
    exact (iteratedFDeriv_const_smul_apply ((hp.of_le (by simp)).contDiffAt)).symm

abbrev SmoothCoefficientJets (dim : ℕ) (r : ℕ) := ↥((smoothCoefficientJetSubmodule dim) r)

 
def coefficientValue (r : ℕ) (F : (SmoothCoefficientJets dim) r) (x : (X dim)) : ℝ :=
  F.1 ⟨0, Nat.zero_lt_succ r⟩ x (fun i => Fin.elim0 i)

theorem coefficientValue_eq (r : ℕ) (F : (SmoothCoefficientJets dim) r)
    (phi : (X dim) → ℝ)
    (hF : ∀ (j : Fin (r + 1)) (x : (X dim)), F.1 j x = iteratedFDeriv ℝ j.val phi x) :
    coefficientValue r F = phi := by
  funext x
  unfold coefficientValue
  rw [hF]
  exact iteratedFDeriv_zero_apply _

theorem contDiff_coefficientValue (r : ℕ) (F : (SmoothCoefficientJets dim) r) :
    ContDiff ℝ ∞ (coefficientValue r F) := by
  obtain ⟨phi, hp, _, hF⟩ := F.2
  rw [coefficientValue_eq r F phi hF]
  exact hp

theorem hasCompactSupport_coefficientValue (r : ℕ) (F : (SmoothCoefficientJets dim) r) :
    HasCompactSupport (coefficientValue r F) := by
  obtain ⟨phi, _, hc, hF⟩ := F.2
  rw [coefficientValue_eq r F phi hF]
  exact hc

theorem coefficientJet_eq_iteratedFDeriv (r : ℕ) (F : (SmoothCoefficientJets dim) r)
    (j : Fin (r + 1)) (x : (X dim)) :
    F.1 j x = iteratedFDeriv ℝ j.val (coefficientValue r F) x := by
  obtain ⟨phi, _, _, hF⟩ := F.2
  rw [coefficientValue_eq r F phi hF]
  exact hF j x

theorem norm_iteratedFDeriv_coefficientValue_le (r : ℕ) (F : (SmoothCoefficientJets dim) r)
    (j : ℕ) (hj : j ≤ r) (x : (X dim)) :
    ‖iteratedFDeriv ℝ j (coefficientValue r F) x‖ ≤ ‖F‖ := by
  let i : Fin (r + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  rw [← coefficientJet_eq_iteratedFDeriv r F i x]
  exact ((F.1 i).norm_coe_le_norm x).trans (norm_le_pi_norm F.1 i)

theorem coefficientValue_add (r : ℕ) (F G : (SmoothCoefficientJets dim) r) :
    coefficientValue r (F + G) = coefficientValue r F + coefficientValue r G := by
  ext x
  rfl

theorem coefficientValue_smul (r : ℕ) (c : ℝ) (F : (SmoothCoefficientJets dim) r) :
    coefficientValue r (c • F) = c • coefficientValue r F := by
  ext x
  rfl

 
def compactCoefficientJet (r : ℕ) (phi : (X dim) → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) : (CoefficientJetSpace dim) r :=
  let M := Classical.choose (hc.exists_bound_iteratedFDeriv hp r)
  let hM := Classical.choose_spec (hc.exists_bound_iteratedFDeriv hp r)
  fun j => BoundedContinuousFunction.mkOfBound
    ⟨iteratedFDeriv ℝ j.val phi, hp.continuous_iteratedFDeriv (by simp)⟩ (2 * M)
    (fun x y => by
      have hj : j.val ≤ r := Nat.le_of_lt_succ j.isLt
      calc
        dist (iteratedFDeriv ℝ j.val phi x) (iteratedFDeriv ℝ j.val phi y)
            ≤ ‖iteratedFDeriv ℝ j.val phi x‖ + ‖iteratedFDeriv ℝ j.val phi y‖ :=
              dist_le_norm_add_norm _ _
        _ ≤ M + M := add_le_add (hM.2 j.val hj x) (hM.2 j.val hj y)
        _ = 2 * M := by ring)

theorem compactCoefficientJet_apply (r : ℕ) (phi : (X dim) → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (j : Fin (r + 1)) (x : (X dim)) :
    compactCoefficientJet r phi hp hc j x = iteratedFDeriv ℝ j.val phi x := rfl

theorem compactCoefficientJet_mem (r : ℕ) (phi : (X dim) → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    compactCoefficientJet r phi hp hc ∈ (smoothCoefficientJetSubmodule dim) r :=
  ⟨phi, hp, hc, fun _ _ => rfl⟩

 
def compactCoefficient (r : ℕ) (phi : (X dim) → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) : (SmoothCoefficientJets dim) r :=
  ⟨compactCoefficientJet r phi hp hc, compactCoefficientJet_mem r phi hp hc⟩

theorem coefficientValue_compactCoefficient (r : ℕ) (phi : (X dim) → ℝ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    coefficientValue r (compactCoefficient r phi hp hc) = phi := by
  funext x
  exact iteratedFDeriv_zero_apply _

end CalderonN.BallDirichlet
