import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
open scoped ContDiff
namespace ShrinkingSpheres
variable {P E J : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]

/-- A common bound on finitely many component jets is the same bound on
    the joint jet with the canonical maximum norm. -/
theorem norm_iteratedFDeriv_fintype_family_le (F : P → J → E) (p : P)
    (hF : ContDiffAt ℝ ∞ F p) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hJets : ∀ j,‖iteratedFDeriv ℝ n (fun x => F x j) p‖ ≤ C) :
    ‖iteratedFDeriv ℝ n F p‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))).mpr
  intro j
  let L : (J → E) →L[ℝ] E := ContinuousLinearMap.proj j
  have hMap := L.iteratedFDeriv_comp_left hF (i:=n) (by simp)
  have hValue := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => P) E => A v) hMap.symm
  change (iteratedFDeriv ℝ n F p v) j = iteratedFDeriv ℝ n (fun x => F x j) p v at hValue
  rw [hValue]
  exact ((iteratedFDeriv ℝ n (fun x => F x j) p).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (hJets j) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))


lemma norm_iteratedFDeriv_product_family_le
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (F : P → A) (G : P → B) (p : P)
    (hF : ContDiffAt ℝ ∞ F p) (hG : ContDiffAt ℝ ∞ G p)
    (n : ℕ) (C : ℝ) (hFJet : ‖iteratedFDeriv ℝ n F p‖ ≤ C)
    (hGJet : ‖iteratedFDeriv ℝ n G p‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun x => (F x,G x)) p‖ ≤ C := by
  rw [iteratedFDeriv_prodMk hF hG (i:=n) (by simp),ContinuousMultilinearMap.opNorm_prod]
  exact max_le hFJet hGJet

end ShrinkingSpheres
