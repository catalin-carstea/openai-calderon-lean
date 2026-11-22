module

public import Proof.CalderonN.ActualRelativeCoefficientGerms
public import Proof.CalderonN.NormalizedStrongPoissonTaylor
public import Proof.CalderonN.CommonSupportOperatorHigherJets

import Proof.CalderonN.ParameterSpatialJetBounds
import Proof.CalderonN.MatrixFieldJetNorms
import Mathlib.Tactic

/-! The signed coefficient Taylor expansion on the actual fixed ball,
transferred to its strong Dirichlet and full divergence operators. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet ShrinkingSpheres
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem joint_matrixEntry_mixed_jets
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a : P × X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (p : P) (z : X dim)
    {N : ℕ} {C : ℝ} (h : LocalSmoothJetBudget a (p,z) N C)
    (i j : I dim) (k n : ℕ) (hkn : n+k ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p' => iteratedFDeriv ℝ k (fun z' => a (p',z') i j) z) p‖ ≤ C := by
  let L := matrixEntryL i j
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    rw [one_mul,matrixEntryL_apply]
    exact Matrix.norm_entry_le_entrywise_sup_norm A (i:=i) (j:=j)
  have hh := norm_iteratedFDeriv_parameter_spatial_jet_le
    (L ∘ a) (L.contDiff.comp ha) p z n k
  have hJ := (h.linear_postcomp L).enlarge (mul_le_of_le_one_left h.nonneg hL)
  exact hh.trans (hJ.bound _ hkn)

theorem local_fixedBall_operator_jet_budgets
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (a : P × X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (J : Set (X dim)) (hJ : IsCompact J) (hSupp : ∀ p z, z ∉ J → a (p,z) = 0)
    (p : P) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ z ∈ closedBall (0:X dim) 1, LocalSmoothJetBudget a (p,z) (N+1) C) :
    let F := commonSupportMatrixFamily 2 a ha J hJ hSupp
    LocalSmoothJetBudget (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)) p N
      (2*strongC1OperatorBudget (fixedSobolevCalculus (dim:=dim))*C) ∧
    LocalSmoothJetBudget (fun t => fullBallDivergenceL 0 (F t)) p N (2*fullC1OperatorBudget (dim:=dim)*C) := by
  dsimp only
  have hMix (n : ℕ) (hn : n ≤ N) (i j : I dim) (k : Fin 2) (z : X dim)
      (hz : z ∈ (fixedBallOpens dim : Set (X dim))) :
      ‖iteratedFDeriv ℝ n (fun p' => iteratedFDeriv ℝ k.val (fun z' => a (p',z') i j) z) p‖ ≤ C :=
    joint_matrixEntry_mixed_jets ha p z (h z (ball_subset_closedBall hz)) i j k.val n (by omega)
  constructor
  · refine ⟨(contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha J hJ hSupp).contDiffAt,
      fun n hn => ?_⟩
    exact norm_iteratedFDeriv_commonSupport_strongOperator_zero_le fixedSobolevCalculus
      a ha J hJ hSupp p n C hC (hMix n hn)
  · refine ⟨(contDiff_fullBallDivergence_family 0 a ha J hJ hSupp).contDiffAt,fun n hn => ?_⟩
    exact norm_iteratedFDeriv_commonSupport_fullOperator_zero_le
      a ha J hJ hSupp p n C hC (hMix n hn)

theorem coefficientMatrixField_affine (F₀ F₁ F₂ : SmoothCoefficientMatrix dim 2) (r : ℝ)
    (z : X dim) :
    coefficientMatrixField 2 (F₀+r • F₁+r^2 • F₂) z =
      coefficientMatrixField 2 F₀ z + r • coefficientMatrixField 2 F₁ z +
        r^2 • coefficientMatrixField 2 F₂ z := by
  ext i j
  change coefficientValue 2 (F₀ i j+r • F₁ i j+r^2 • F₂ i j) z = _
  simp only [coefficientValue_add,coefficientValue_smul,Pi.add_apply,Pi.smul_apply,
    coefficientMatrixField,Matrix.add_apply,Matrix.smul_apply]

/-- The same two operator families are the affine and quadratic terms
in the actual strong fixed-ball coefficient near the physical radius. -/
theorem uniform_actual_relativeStrongOperator_jets (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (F₀ : SmoothCoefficientMatrix dim 2)
    (hFlat : ∀ z ∈ closedBall (0:X dim) 2, coefficientMatrixField 2 F₀ z = 1) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∃ (F₁ F₂ : X dim × ℝ → SmoothCoefficientMatrix dim 2) (V : Set (X dim × ℝ))
        (Z : Set (X dim)),
        IsOpen V ∧ (y,0) ∈ V ∧ IsOpen Z ∧ closedBall (0:X dim) 1 ⊆ Z ∧
        (∀ p ∈ V,∀ z ∈ Z, coefficientMatrixField 2
          (F₀+(d.radius y) • F₁ p+(d.radius y)^2 • F₂ p) z =
          actualFramedCoefficientField d (actualRelativeCoefficientInput (d.radius y) (p,z))) ∧
        LocalSmoothJetBudget (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F₁ p)) (y,0) N C ∧
        LocalSmoothJetBudget (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F₂ p)) (y,0) N C ∧
        LocalSmoothJetBudget (fun p => fullBallDivergenceL 0 (F₁ p)) (y,0) N C ∧
        LocalSmoothJetBudget (fun p => fullBallDivergenceL 0 (F₂ p)) (y,0) N C := by
  obtain ⟨η,C₁,C₂,hη,hC₁,hC₂,hRel⟩ := uniform_actual_relativeCoefficient_germs
    hn hY hΩ hYc (N+1) (by omega) K ρ c₀ M Cj hK hρ
  let SB := strongC1OperatorBudget (fixedSobolevCalculus (dim:=dim))
  let FB := fullC1OperatorBudget (dim:=dim)
  let C := 2*(SB+FB)*(C₁+C₂)
  have hSB : 0 ≤ SB := strongC1OperatorBudget_nonneg _
  have hFB : 0 ≤ FB := fullC1OperatorBudget_nonneg
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε he hs d hd hdFrame y hy
  obtain ⟨a₁,a₂,J,W,ha₁,ha₂,hJ,hSupp,hW,hCW,_,_,hEq,hJet⟩ :=
    hRel floor hf ε he hs d hd hdFrame y hy
  let p₀ : X dim × ℝ := (y,0)
  let r := d.radius y
  have hSupp₁ (p : X dim × ℝ) (z : X dim) (hz : z ∉ J) := (hSupp p z hz).1
  have hSupp₂ (p : X dim × ℝ) (z : X dim) (hz : z ∉ J) := (hSupp p z hz).2
  let F₁ := commonSupportMatrixFamily 2 a₁ ha₁ J hJ hSupp₁
  let F₂ := commonSupportMatrixFamily 2 a₂ ha₂ J hJ hSupp₂
  obtain ⟨V,B,hV,hB,hpV,hCB,hVB⟩ := generalized_tube_lemma
    (isCompact_singleton (x:=p₀)) (isCompact_closedBall (0:X dim) 1) hW hCW
  let Z := B ∩ ball (0:X dim) 2
  have hZ : IsOpen Z := hB.inter isOpen_ball
  have hCZ : closedBall (0:X dim) 1 ⊆ Z :=
    subset_inter hCB (closedBall_subset_ball (by norm_num))
  obtain ⟨hS₁,hT₁⟩ := local_fixedBall_operator_jet_budgets a₁ ha₁ J hJ hSupp₁ p₀ N C₁ hC₁
    (fun z hz => (hJet z hz).1)
  obtain ⟨hS₂,hT₂⟩ := local_fixedBall_operator_jet_budgets a₂ ha₂ J hJ hSupp₂ p₀ N C₂ hC₂
    (fun z hz => (hJet z hz).2)
  refine ⟨F₁,F₂,V,Z,hV,hpV (mem_singleton _),hZ,hCZ,?_,?_,?_,?_,?_⟩
  · intro p hp z hz
    rw [coefficientMatrixField_affine,hFlat z (ball_subset_closedBall hz.2)]
    simp only [F₁,F₂,coefficientMatrixField_commonSupportMatrixFamily]
    exact (hEq (p,z) (hVB ⟨hp,hz.1⟩)).symm
  · exact hS₁.enlarge (by dsimp only [C,SB,FB]; nlinarith [mul_nonneg hSB hC₂,mul_nonneg hFB hC₁,mul_nonneg hFB hC₂])
  · exact hS₂.enlarge (by dsimp only [C,SB,FB]; nlinarith [mul_nonneg hSB hC₁,mul_nonneg hFB hC₁,mul_nonneg hFB hC₂])
  · exact hT₁.enlarge (by dsimp only [C,SB,FB]; nlinarith [mul_nonneg hSB hC₁,mul_nonneg hSB hC₂,mul_nonneg hFB hC₂])
  · exact hT₂.enlarge (by dsimp only [C,SB,FB]; nlinarith [mul_nonneg hSB hC₁,mul_nonneg hSB hC₂,mul_nonneg hFB hC₁])

end CalderonN
