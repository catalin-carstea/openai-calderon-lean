module

public import Proof.CalderonN.TaylorJetCalculus

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option maxHeartbeats 1600000 in
private theorem taylorJet_cons_cons_comm {D : Set E} {f : E → F}
    (hD : UniqueDiffOn ℝ D) (hInt : D ⊆ closure (interior D))
    (hf : ContDiffOn ℝ ∞ f D) (k : ℕ) (x : E) (hx : x ∈ D)
    (a b : E) (v : Fin k → E) :
    iteratedFDerivWithin ℝ (k+2) f D x (Fin.cons a (Fin.cons b v)) =
      iteratedFDerivWithin ℝ (k+2) f D x (Fin.cons b (Fin.cons a v)) := by
  let G := iteratedFDerivWithin ℝ k f D
  let H (z : E) := G z v
  have hG := contDiffOn_iteratedFDerivWithin_top hf hD k
  let L : (E [×k]→L[ℝ] F) →L[ℝ] F :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) F v
  have hH : ContDiffOn ℝ ∞ H D := show ContDiffOn ℝ ∞ (L ∘ G) D from L.contDiff.comp_contDiffOn hG
  have h₁ (c : E) (z : E) (hz : z ∈ D) :
      fderivWithin ℝ H D z c = iteratedFDerivWithin ℝ (k+1) f D z (Fin.cons c v) := by
    have h := ((hG.differentiableOn (by simp) z hz).hasFDerivWithinAt.continuousMultilinear_apply_const v).fderivWithin (hD z hz)
    rw [show H = fun y => G y v from rfl,h,iteratedFDerivWithin_succ_apply_left]
    rfl
  have h₂ (c d : E) :
      fderivWithin ℝ (fderivWithin ℝ H D) D x c d =
        iteratedFDerivWithin ℝ (k+2) f D x (Fin.cons c (Fin.cons d v)) := by
    have h := (((hH.fderivWithin hD (m := ∞) (by simp)).differentiableOn (by simp) x hx).hasFDerivWithinAt.clm_apply (hasFDerivWithinAt_const d x D)).fderivWithin (hD x hx)
    have hEval : (fderivWithin ℝ (fun z => fderivWithin ℝ H D z d) D x) c =
        fderivWithin ℝ (fderivWithin ℝ H D) D x c d := by
      rw [h]
      simp
    rw [← hEval, fderivWithin_congr (h₁ d) (h₁ d x hx),iteratedFDerivWithin_succ_apply_left]
    have hG' := contDiffOn_iteratedFDerivWithin_top hf hD (k+1)
    have hh := ((hG'.differentiableOn (by simp) x hx).hasFDerivWithinAt.continuousMultilinear_apply_const (Fin.cons d v)).fderivWithin (hD x hx)
    rw [hh]
    rfl
  have hSym := (hH x hx).isSymmSndFDerivWithinAt (by simp) hD (hInt hx) hx
  rw [← h₂,← h₂]
  exact hSym a b

set_option maxHeartbeats 1600000 in
/-- The higher real derivative on a regular closed domain is symmetric
under all permutations. The two leading slots commute by the second
derivative theorem. Permutations of the tail commute with differentiation. -/
theorem iteratedFDerivWithin_perm {D : Set E} {f : E → F}
    (hD : UniqueDiffOn ℝ D) (hInt : D ⊆ closure (interior D))
    (hf : ContDiffOn ℝ ∞ f D) :
    ∀ (k : ℕ) (x : E), x ∈ D → ∀ (v : Fin k → E) (σ : Equiv.Perm (Fin k)),
      iteratedFDerivWithin ℝ k f D x (v ∘ σ) =
        iteratedFDerivWithin ℝ k f D x v := by
  intro k
  induction k with
  | zero =>
    intro x hx v σ
    rw [show v ∘ σ = v from Subsingleton.elim _ _]
  | succ k ih =>
    let H (z : E) := iteratedFDerivWithin ℝ (k+1) f D z
    let G (z : E) := iteratedFDerivWithin ℝ k f D z
    have hG := contDiffOn_iteratedFDerivWithin_top hf hD k
    have hTail (x : E) (hx : x ∈ D) (a : E) (v : Fin k → E) (σ : Equiv.Perm (Fin k)) :
        H x (Fin.cons a (v ∘ σ)) = H x (Fin.cons a v) := by
      have h (w : Fin k → E) :
          fderivWithin ℝ (fun z => G z w) D x a = H x (Fin.cons a w) := by
        have hd := ((hG.differentiableOn (by simp) x hx).hasFDerivWithinAt.continuousMultilinear_apply_const w).fderivWithin (hD x hx)
        rw [hd]
        simp only [H,iteratedFDerivWithin_succ_apply_left,Fin.cons_zero,Fin.tail_cons]
        rfl
      rw [← h,← h, fderivWithin_congr (fun z hz => ih z hz v σ) (ih x hx v σ)]
    intro x hx
    let S : Submonoid (Equiv.Perm (Fin (k+1))) :=
      { carrier := {σ | ∀ v, H x (v ∘ σ) = H x v}
        one_mem' := fun _ => rfl
        mul_mem' := fun hσ hτ v => (hτ (v ∘ _)).trans (hσ v) }
    have hGen : Set.range (fun i : Fin k => Equiv.swap i.castSucc i.succ) ⊆ S := by
      rintro _ ⟨i,rfl⟩ v
      cases k with
      | zero => exact i.elim0
      | succ k =>
        refine Fin.cases ?_ (fun j => ?_) i
        · change H x (v ∘ Equiv.swap 0 1) = H x v
          let w := Fin.tail (Fin.tail v)
          have he : v = Fin.cons (v 0) (Fin.cons (v 1) w) := by
            ext z
            refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => ?_) j) z <;> simp [w,Fin.tail_def]
          rw [he]
          rw [show Fin.cons (v 0) (Fin.cons (v 1) w) ∘ Equiv.swap 0 1 =
                Fin.cons (v 1) (Fin.cons (v 0) w) from Matrix.cons_cons_comp_swap_zero_one _ _ _]
          exact taylorJet_cons_cons_comm hD hInt hf k x hx _ _ _
        · have he : v = Fin.cons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
          change H x (v ∘ Equiv.swap (Fin.succ j).castSucc (Fin.succ j).succ) = H x v
          rw [← Fin.succ_castSucc]
          calc
            _ = H x (Fin.cons (v 0) (Fin.tail v ∘ Equiv.swap j.castSucc j.succ)) := by
              congr 1
              conv_lhs => rw [he]
              exact (Matrix.cons_swap _ _ _ _).symm
            _ = _ := (hTail x hx _ _ _).trans (congrArg (H x) he.symm)
    have hTop : (⊤ : Submonoid (Equiv.Perm (Fin (k+1)))) ≤ S := by
      rw [← Equiv.Perm.mclosure_swap_castSucc_succ k]
      exact Submonoid.closure_le.mpr hGen
    intro v σ
    exact hTop (Submonoid.mem_top σ) v

end CalderonN
