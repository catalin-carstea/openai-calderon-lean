module

public import Proof.CalderonN.WeakEnergyPoissonDifferenceJets
public import Proof.CalderonN.LiftedPoissonTaylorJets

import Mathlib.Tactic

/-! Uniform neighborhood and quadratic jet budget for the weak conormal
response of an affine coefficient family. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {P H Z F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_weakConormal_taylor_jet_budget
    (j : Z →L[ℝ] H) (E₀ : H →L[ℝ] H →L[ℝ] ℝ) (P₀ : F →L[ℝ] H)
    (hInv₀ : (weakEnergyZeroOperatorL j E₀).IsInvertible)
    (hFlat : ∀ u v,E₀ (P₀ u) (j v) = 0)
    (hOrtho : ∀ u v,E₀ (j u) (P₀ v) = 0)
    (N : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) δ, ∀ x : P,
      ∀ E₁ E₂ : P → H →L[ℝ] H →L[ℝ] ℝ,
      LocalSmoothJetBudget E₁ x N D → LocalSmoothJetBudget E₂ x N D →
      let E (p : P) := E₀+r • E₁ p+r^2 • E₂ p
      (∀ᶠ p in 𝓝 x,(weakEnergyZeroOperatorL j (E p)).IsInvertible) ∧
      LocalSmoothJetBudget (fun p => (E p).bilinearComp (weakEnergyPoissonOperatorL j (E p) P₀) P₀-
        E₀.bilinearComp P₀ P₀-r • (E₁ p).bilinearComp P₀ P₀) x N (C*r^2) := by
  let S := weakEnergyZeroOperatorL j
  obtain ⟨δ,I,hδ,hI,hδ₁,hI₀,hInv⟩ :=
    exists_uniform_affine_operator_inverse_near (S E₀) hInv₀ (‖S‖*D) (by positivity)
  let B := max 0 (weakEnergyPoissonDifferenceBudget j E₀ P₀ N D I)
  let L := weakConormalBilinearL P₀
  let C := (2:ℝ)^N*‖L‖*(2*D*B)+‖L.flip P₀‖*D
  have hB : 0 ≤ B := le_max_left _ _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨δ,C,hδ,hC,?_⟩
  intro r hr x E₁ E₂ hE₁ hE₂
  dsimp only
  let E (p : P) := E₀+r • E₁ p+r^2 • E₂ p
  have hT (A : H →L[ℝ] H →L[ℝ] ℝ) (h : ‖A‖ ≤ D) : ‖S A‖ ≤ ‖S‖*D :=
    (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
  obtain ⟨hInvertible,hIAt⟩ := hInv r hr (S (E₁ x)) (S (E₂ x))
    (hT _ hE₁.value_norm_le) (hT _ hE₂.value_norm_le)
  have hEq : S (E x) = S E₀+r • S (E₁ x)+r^2 • S (E₂ x) := by
    simp only [E,map_add,map_smul]
  rw [← hEq] at hInvertible hIAt
  have hE : ContDiffAt ℝ ∞ E x :=
    (contDiffAt_const.add (hE₁.smooth.const_smul _)).add (hE₂.smooth.const_smul _)
  have hNear : ∀ᶠ p in 𝓝 x,(S (E p)).IsInvertible :=
    (S.continuous.continuousAt.comp hE.continuousAt).eventually hInvertible.eventually_nhds
  have hU := localWeakEnergyPoissonDifference_budget j E₀ E₁ E₂ P₀ x r N D I hr.1
    (hr.2.trans hδ₁) hI hE₁ hE₂ hInv₀ hI₀ hInvertible hIAt hFlat
  have hU' : LocalSmoothJetBudget (fun p => weakEnergyPoissonOperatorL j (E p) P₀-P₀) x N (B*r) :=
    hU.enlarge (show weakEnergyPoissonDifferenceBudget j E₀ P₀ N D I*r ≤ B*r from
      mul_le_mul_of_nonneg_right (le_max_right _ _) hr.1)
  have hOrth (p : P) :
      E₀.bilinearComp (weakEnergyPoissonOperatorL j (E p) P₀-P₀) P₀ = 0 := by
    ext f g : 2
    rw [ContinuousLinearMap.bilinearComp_apply]
    simp only [weakEnergyPoissonOperatorL,ContinuousLinearMap.sub_apply,zero_apply,
      ContinuousLinearMap.comp_apply,sub_sub_cancel_left,map_neg,neg_apply,hOrtho,neg_zero]
  have hJet := localWeakConormalTaylor_budget E₀ E₁ E₂ P₀ (fun p => weakEnergyPoissonOperatorL j (E p) P₀)
    x r N D B hr.1 (hr.2.trans hδ₁) hE₁ hE₂ hU' hOrth
  exact ⟨hNear,hJet⟩

end CalderonN
