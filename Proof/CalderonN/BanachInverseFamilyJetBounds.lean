module

public import Proof.CalderonN.BanachResolventJetBounds
public import Proof.CalderonN.FiniteJetBoundCalculus

/-! From BanachInverseFamilyJetBounds in the checked Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def inverseFamilyInputL (e : E ≃L[ℝ] F) : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ E F E) (e.symm : F →L[ℝ] E)

def inverseFamilyOutputL (e : E ≃L[ℝ] F) : (E →L[ℝ] E) →L[ℝ] (F →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ F E E).flip (e.symm : F →L[ℝ] E)

lemma norm_inverseFamilyInputL_le (e : E ≃L[ℝ] F) : ‖inverseFamilyInputL e‖ ≤ ‖(e.symm : F →L[ℝ] E)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro A
  exact ContinuousLinearMap.opNorm_comp_le _ _

lemma norm_inverseFamilyOutputL_le (e : E ≃L[ℝ] F) : ‖inverseFamilyOutputL e‖ ≤ ‖(e.symm : F →L[ℝ] E)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro A
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

lemma operatorInverse_centered_resolvent_identity [CompleteSpace E]
    (e : E ≃L[ℝ] F) (A : E →L[ℝ] F) :
    A.inverse = inverseFamilyOutputL e (operatorResolvent (1-inverseFamilyInputL e A)) := by
  rw [ContinuousLinearMap.inverse_eq_ringInverse e A]
  have hAff : (1:E →L[ℝ] E)-(1-inverseFamilyInputL e A) = inverseFamilyInputL e A := by abel
  rw [operatorResolvent,hAff]
  rfl

lemma norm_iteratedFDeriv_const_sub_pos
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : P → V) (x : P) (hf : ContDiffAt ℝ ∞ f x) (c : V) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun y => c-f y) x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  change ‖iteratedFDeriv ℝ n ((fun _ : P => c)-f) x‖ = _
  rw [iteratedFDeriv_sub_apply (f:=fun _ : P => c) (g:=f) contDiffAt_const (hf.of_le (by simp)),
    iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,zero_sub,norm_neg]

/-- Uniform finite jets of an actual inverse family, including order zero,
    from the bounded inverse at the selected point and the input operator
    jets. The inverse is the canonical ContinuousLinearMap.inverse. -/
theorem norm_iteratedFDeriv_inverse_family_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace E]
    (A : P → E →L[ℝ] F) (e : E ≃L[ℝ] F) (x : P)
    (hBase : A x = (e : E →L[ℝ] F)) (hA : ContDiffAt ℝ ∞ A x)
    (N : ℕ) (I D : ℝ) (hI : 0 ≤ I) (hD : 0 ≤ D)
    (hInv : ‖(e.symm : F →L[ℝ] E)‖ ≤ I)
    (hJets : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j A x‖ ≤ D)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun q => (A q).inverse) x‖ ≤
      I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*D)^N) := by
  let B : P → E →L[ℝ] E := fun q => 1-inverseFamilyInputL e (A q)
  let DB := 1+I*D
  have hDB : 1 ≤ DB := by
    have hh : 0 ≤ I*D := mul_nonneg hI hD
    dsimp only [DB]
    linarith only [hh]
  have hInputNorm : ‖inverseFamilyInputL e‖ ≤ I := (norm_inverseFamilyInputL_le e).trans hInv
  have hOutputNorm : ‖inverseFamilyOutputL e‖ ≤ I := (norm_inverseFamilyOutputL_le e).trans hInv
  have hLA : ContDiffAt ℝ ∞ ((inverseFamilyInputL e) ∘ A) x := (inverseFamilyInputL e).contDiff.contDiffAt.comp x hA
  have hB : ContDiffAt ℝ ∞ B x := contDiffAt_const.sub hLA
  have hB0 : B x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    change v-e.symm (A x v) = 0
    rw [hBase]
    simp
  have hBJets (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) : ‖iteratedFDeriv ℝ j B x‖ ≤ DB := by
    have hEq := norm_iteratedFDeriv_const_sub_pos ((inverseFamilyInputL e) ∘ A) x hLA (1:E →L[ℝ] E) j hj
    change ‖iteratedFDeriv ℝ j B x‖ = _ at hEq
    rw [hEq]
    have hh := norm_iteratedFDeriv_clm_comp_le (inverseFamilyInputL e) A x hA j
    exact hh.trans ((mul_le_mul hInputNorm (hJets j hj hjN) (norm_nonneg _) hI).trans
      (by dsimp only [DB];linarith))
  have hRes : ContDiffAt ℝ ∞ (operatorResolvent (E:=E)) (B x) := by
    rw [hB0]
    exact contDiffAt_operatorResolvent_zero
  have hOuter (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j (operatorResolvent (E:=E)) (B x)‖ ≤ (N.factorial:ℝ) := by
    rw [hB0]
    exact operatorResolvent_finite_jet_bound N j hj
  have hCommon := iteratedFDeriv_comp_common_bound B (operatorResolvent (E:=E)) x hB hRes
    N (N.factorial:ℝ) DB (Nat.cast_nonneg _) hDB hOuter hBJets n hn
  have hRepresentation : (fun q => (A q).inverse) = inverseFamilyOutputL e ∘ (operatorResolvent ∘ B) := by
    funext q
    exact operatorInverse_centered_resolvent_identity e (A q)
  rw [hRepresentation]
  have hh := norm_iteratedFDeriv_clm_comp_le (inverseFamilyOutputL e) (operatorResolvent ∘ B) x (hRes.comp x hB) n
  exact hh.trans (mul_le_mul hOutputNorm hCommon (norm_nonneg _) hI)

theorem norm_iteratedFDeriv_inverse_family_le_of_isInvertible
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace E]
    (A : P → E →L[ℝ] F) (x : P) (hAx : (A x).IsInvertible) (hA : ContDiffAt ℝ ∞ A x)
    (N : ℕ) (I D : ℝ) (hI : 0 ≤ I) (hD : 0 ≤ D)
    (hInv : ‖(A x).inverse‖ ≤ I)
    (hJets : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j A x‖ ≤ D)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun q => (A q).inverse) x‖ ≤
      I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*D)^N) := by
  obtain ⟨e,he⟩ := hAx
  have hInvE : ‖(e.symm : F →L[ℝ] E)‖ ≤ I := by
    rw [← he,ContinuousLinearMap.inverse_equiv] at hInv
    exact hInv
  exact norm_iteratedFDeriv_inverse_family_le A e x he.symm hA N I D hI hD hInvE hJets n hn

end ShrinkingSpheres
