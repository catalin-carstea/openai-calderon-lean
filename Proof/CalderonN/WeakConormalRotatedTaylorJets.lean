module

public import Proof.CalderonN.WeakConormalUniformJets

import Mathlib.Tactic

/-! The rotational commutator uses the rotated coefficient tested
against two actual Poisson solutions. Subtracting its flat affine
part gives a quadratic mixed-parameter jet bound. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {P H F Z : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

private def weakEnergyRightPrecompL :
    (F →L[ℝ] H →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] H) →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ :=
  let A := (ContinuousLinearMap.flipₗᵢ ℝ F H ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let B := (ContinuousLinearMap.flipₗᵢ ℝ F F ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let C := ContinuousLinearMap.compL ℝ F H (F →L[ℝ] ℝ)
  ((ContinuousLinearMap.compL ℝ (F →L[ℝ] H) (F →L[ℝ] F →L[ℝ] ℝ) (F →L[ℝ] F →L[ℝ] ℝ)) B).comp
    (C.comp A)

private theorem weakEnergyRightPrecompL_apply
    (E : F →L[ℝ] H →L[ℝ] ℝ) (U : F →L[ℝ] H) (f g : F) :
    weakEnergyRightPrecompL E U f g = E f (U g) := by
  simp only [weakEnergyRightPrecompL,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_flipₗᵢ,ContinuousLinearMap.flip_apply]

private theorem localSmoothJetBudget_bilinearComp
    {E : P → H →L[ℝ] H →L[ℝ] ℝ} {U V : P → F →L[ℝ] H} {x : P} {N : ℕ} {A B C : ℝ}
    (hE : LocalSmoothJetBudget E x N A) (hU : LocalSmoothJetBudget U x N B)
    (hV : LocalSmoothJetBudget V x N C) :
    LocalSmoothJetBudget (fun p => (E p).bilinearComp (U p) (V p)) x N
      (((2:ℝ)^N*‖weakEnergyRightPrecompL (F:=F) (H:=H)‖)*
        (((2:ℝ)^N*‖ContinuousLinearMap.compL ℝ F H (H →L[ℝ] ℝ)‖)*A*B)*C) := by
  let L := ContinuousLinearMap.compL ℝ F H (H →L[ℝ] ℝ)
  have h := (hE.bilinear hU L).bilinear hV weakEnergyRightPrecompL
  have hEq : (fun p => weakEnergyRightPrecompL (L (E p) (U p)) (V p)) =
      (fun p => (E p).bilinearComp (U p) (V p)) := by
    funext p
    ext f g : 2
    simp only [weakEnergyRightPrecompL_apply,L,ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.bilinearComp_apply]
  rwa [hEq] at h

private theorem localWeakConormalRotatedTaylor_budget
    (P₀ : F →L[ℝ] H) (U : P → F →L[ℝ] H)
    (T₁ T₂ : P → H →L[ℝ] H →L[ℝ] ℝ)
    (x : P) (r : ℝ) (N : ℕ) (A B : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hB : 0 ≤ B)
    (hT₁ : LocalSmoothJetBudget T₁ x N A) (hT₂ : LocalSmoothJetBudget T₂ x N A)
    (hU : LocalSmoothJetBudget (fun p => U p-P₀) x N (B*r)) :
    let C := ((2:ℝ)^N*‖weakEnergyRightPrecompL (F:=F) (H:=H)‖)*
      ((2:ℝ)^N*‖ContinuousLinearMap.compL ℝ F H (H →L[ℝ] ℝ)‖)
    let D := C*(2*A*B*(‖P₀‖+B)+2*A*‖P₀‖*B+A*‖P₀‖^2)
    LocalSmoothJetBudget (fun p => (r • T₁ p+r^2 • T₂ p).bilinearComp (U p) (U p)-
      r • (T₁ p).bilinearComp P₀ P₀) x N (D*r^2) := by
  dsimp only
  let C := ((2:ℝ)^N*‖weakEnergyRightPrecompL (F:=F) (H:=H)‖)*
    ((2:ℝ)^N*‖ContinuousLinearMap.compL ℝ F H (H →L[ℝ] ℝ)‖)
  let T (p : P) := r • T₁ p+r^2 • T₂ p
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hT : LocalSmoothJetBudget T x N (2*A*r) := by
    have h := (hT₁.const_smul r hr).add (hT₂.const_smul (r^2) (sq_nonneg r))
    apply h.enlarge
    have hSz : r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hr₁ hr]
    calc
      r*A+r^2*A ≤ r*A+r*A := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hSz hT₁.nonneg)
      _ = 2*A*r := by ring
  have hP : LocalSmoothJetBudget (fun _ : P => P₀) x N ‖P₀‖ := LocalSmoothJetBudget.const _
  have hU' : LocalSmoothJetBudget U x N (‖P₀‖+B) := by
    have h := hP.add hU
    simp only [add_sub_cancel] at h
    exact h.enlarge (add_le_add (le_refl _) (mul_le_of_le_one_right hB hr₁))
  have h₁ := localSmoothJetBudget_bilinearComp hT hU hU'
  have h₂ := localSmoothJetBudget_bilinearComp hT hP hU
  have h₃ := (localSmoothJetBudget_bilinearComp hT₂ hP hP).const_smul (r^2) (sq_nonneg r)
  have hEq : (fun p => (T p).bilinearComp (U p) (U p)-r • (T₁ p).bilinearComp P₀ P₀) =
      fun p => (T p).bilinearComp (U p-P₀) (U p)+(T p).bilinearComp P₀ (U p-P₀)+
        r^2 • (T₂ p).bilinearComp P₀ P₀ := by
    funext p
    ext f g : 2
    simp only [ContinuousLinearMap.bilinearComp_apply,T,sub_apply,add_apply,smul_apply,smul_eq_mul,
      map_sub]
    ring
  rw [hEq]
  convert (h₁.add h₂).add h₃ using 1 <;> ring

theorem exists_weakConormal_rotatedTaylor_jet_budget
    (j : Z →L[ℝ] H) (E₀ : H →L[ℝ] H →L[ℝ] ℝ) (P₀ : F →L[ℝ] H)
    (hInv₀ : (weakEnergyZeroOperatorL j E₀).IsInvertible)
    (hFlat : ∀ u v,E₀ (P₀ u) (j v) = 0)
    (N : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ r ∈ Icc (0:ℝ) δ, ∀ x : P,
      ∀ E₁ E₂ T₁ T₂ : P → H →L[ℝ] H →L[ℝ] ℝ,
      LocalSmoothJetBudget E₁ x N D → LocalSmoothJetBudget E₂ x N D →
      LocalSmoothJetBudget T₁ x N D → LocalSmoothJetBudget T₂ x N D →
      let E (p : P) := E₀+r • E₁ p+r^2 • E₂ p
      let U (p : P) := weakEnergyPoissonOperatorL j (E p) P₀
      LocalSmoothJetBudget (fun p => (r • T₁ p+r^2 • T₂ p).bilinearComp (U p) (U p)-
        r • (T₁ p).bilinearComp P₀ P₀) x N (C*r^2) := by
  let S := weakEnergyZeroOperatorL j
  obtain ⟨δ,I,hδ,hI,hδ₁,hI₀,hInv⟩ :=
    exists_uniform_affine_operator_inverse_near (S E₀) hInv₀ (‖S‖*D) (by positivity)
  let B := max 0 (weakEnergyPoissonDifferenceBudget j E₀ P₀ N D I)
  let A := ((2:ℝ)^N*‖weakEnergyRightPrecompL (F:=F) (H:=H)‖)*
    ((2:ℝ)^N*‖ContinuousLinearMap.compL ℝ F H (H →L[ℝ] ℝ)‖)
  let C := A*(2*D*B*(‖P₀‖+B)+2*D*‖P₀‖*B+D*‖P₀‖^2)
  have hB : 0 ≤ B := le_max_left _ _
  have hC : 0 ≤ C := by dsimp only [C,A]; positivity
  refine ⟨δ,C,hδ,hC,?_⟩
  intro r hr x E₁ E₂ T₁ T₂ hE₁ hE₂ hT₁ hT₂
  dsimp only
  let E (p : P) := E₀+r • E₁ p+r^2 • E₂ p
  have hT (L : H →L[ℝ] H →L[ℝ] ℝ) (h : ‖L‖ ≤ D) : ‖S L‖ ≤ ‖S‖*D :=
    (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
  obtain ⟨hInvertible,hIAt⟩ := hInv r hr (S (E₁ x)) (S (E₂ x))
    (hT _ hE₁.value_norm_le) (hT _ hE₂.value_norm_le)
  have hEq : S (E x) = S E₀+r • S (E₁ x)+r^2 • S (E₂ x) := by
    simp only [E,map_add,map_smul]
  rw [← hEq] at hInvertible hIAt
  have hU := localWeakEnergyPoissonDifference_budget j E₀ E₁ E₂ P₀ x r N D I hr.1
    (hr.2.trans hδ₁) hI hE₁ hE₂ hInv₀ hI₀ hInvertible hIAt hFlat
  have hU' : LocalSmoothJetBudget (fun p => weakEnergyPoissonOperatorL j (E p) P₀-P₀) x N (B*r) :=
    hU.enlarge (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.1)
  exact localWeakConormalRotatedTaylor_budget P₀ _ T₁ T₂ x r N D B hr.1 (hr.2.trans hδ₁) hB hT₁ hT₂ hU'

end CalderonN
