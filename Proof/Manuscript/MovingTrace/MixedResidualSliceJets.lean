module

public import Proof.CalderonN.MixedSliceJets
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CalderonN
open scoped ContDiff

namespace CalderonPaper

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The inner and outer arguments of a nested derivative form one list
of directions. The first direction of the outer derivative is prepended. -/
private def mixedDirections {E : Type} (k : ℕ) (u : Fin k → E) :
    (j : ℕ) → (Fin j → E) → Fin (k+j) → E
  | 0, _ => u
  | j+1, v => Fin.cons (v 0) (mixedDirections k u j (Fin.tail v))

private theorem mixedDirections_prod {E : Type} [NormedAddCommGroup E]
    (k : ℕ) (u : Fin k → E) (j : ℕ) (v : Fin j → E) :
    (∏ i, ‖mixedDirections k u j v i‖) = (∏ i, ‖v i‖) * (∏ i, ‖u i‖) := by
  induction j with
  | zero => simp [mixedDirections]
  | succ j ih =>
    change (∏ i : Fin (k+j+1), ‖(@Fin.cons (k+j) (fun _ => E) (v 0)
        (mixedDirections k u j (Fin.tail v))) i‖) =
      (∏ i : Fin (j+1), ‖v i‖) * (∏ i, ‖u i‖)
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,ih,mul_assoc,Fin.tail]

private theorem iteratedFDeriv_iterated_apply
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (k : ℕ) (u : Fin k → E)
    (j : ℕ) (x : E) (v : Fin j → E) :
    (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f) x v) u =
      iteratedFDeriv ℝ (k+j) f x (mixedDirections k u j v) := by
  induction j generalizing x with
  | zero => simp [mixedDirections,iteratedFDeriv_zero_apply]
  | succ j ih =>
    have hF : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f) := hf.iteratedFDeriv_right (by simp)
    have hJ : ContDiff ℝ ∞ (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f)) :=
      hF.iteratedFDeriv_right (by simp)
    have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f)) x :=
      hJ.differentiable (by simp) x
    rw [hD.iteratedFDeriv_succ_apply_left']
    have hE : DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ j
        (iteratedFDeriv ℝ k f) y (Fin.tail v)) x :=
      hD.continuousMultilinear_apply_const _
    rw [← fderiv_continuousMultilinear_apply_const_apply hE u (v 0)]
    have hEq : (fun y => (iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f) y (Fin.tail v)) u) =
        (fun y => iteratedFDeriv ℝ (k+j) f y (mixedDirections k u j (Fin.tail v))) :=
      funext fun y => ih y (Fin.tail v)
    rw [hEq]
    have hK : DifferentiableAt ℝ (iteratedFDeriv ℝ (k+j) f) x :=
      (hf.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hS := hK.iteratedFDeriv_succ_apply_left' (n := k+j)
      (m := @Fin.cons (k+j) (fun _ => E) (v 0) (mixedDirections k u j (Fin.tail v)))
    simpa only [mixedDirections,Fin.tail_cons,Fin.cons_zero,Nat.add_succ] using hS.symm

/-- A higher derivative of the iterated Fréchet derivative is bounded by
the single Fréchet derivative of the sum of the two orders. -/
theorem norm_iteratedFDeriv_of_iteratedFDeriv_le (j k : ℕ)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (x : E) :
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ k f) x‖ ≤ ‖iteratedFDeriv ℝ (j+k) f x‖ := by
  rw [Nat.add_comm j k]
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) ?_
  intro v
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _))) ?_
  intro u
  rw [iteratedFDeriv_iterated_apply hf,mul_assoc,← mixedDirections_prod]
  exact (iteratedFDeriv ℝ (k+j) f x).le_opNorm _

/-- The mixed parameter/spatial derivative is a restriction of the joint
derivative and its norm is bounded by the norm of that joint derivative. -/
theorem norm_mixedSlice_iteratedFDeriv_le {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E × G → F}
    (hf : ContDiff ℝ ∞ f) (p : E) (z : G) (j k : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q : E => iteratedFDeriv ℝ k (fun w : G => f (q,w)) z) p‖ ≤
      ‖iteratedFDeriv ℝ (j+k) f (p,z)‖ := by
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (F := F)
    (fun _ : Fin k => ContinuousLinearMap.inr ℝ E G)
  have hL : ‖L‖ ≤ 1 := (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le F _).trans
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ E G))
  let d := iteratedFDeriv ℝ k f
  have hd : ContDiff ℝ ∞ d := hf.iteratedFDeriv_right (by simp)
  let m (q : E) := (q,z)
  have hm : ContDiff ℝ ∞ m := contDiff_id.prodMk contDiff_const
  have hEq : (fun q : E => iteratedFDeriv ℝ k (fun w : G => f (q,w)) z) = L ∘ d ∘ m :=
    funext fun q => iteratedFDeriv_slice_right_eq hf q z k
  rw [hEq]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (d ∘ m) p‖ :=
      L.norm_iteratedFDeriv_comp_left (hd.comp hm).contDiffAt (by simp)
    _ ≤ ‖iteratedFDeriv ℝ j (d ∘ m) p‖ := mul_le_of_le_one_left (norm_nonneg _) hL
    _ ≤ ‖iteratedFDeriv ℝ j d (p,z)‖ := norm_iteratedFDeriv_slice_left_le hd p z j
    _ ≤ _ := norm_iteratedFDeriv_of_iteratedFDeriv_le j k hf (p,z)

end CalderonPaper
