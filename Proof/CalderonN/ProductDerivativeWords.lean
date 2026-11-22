module

public import Proof.CalderonN.ProductHarmonicDerivatives

import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

public section

set_option maxHeartbeats 1500000

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {d : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def directionalWord : List E → (E → ℝ) → E → ℝ
  | [], f => f
  | v :: w, f => fun x => fderiv ℝ (directionalWord w f) x v

theorem contDiff_directionalWord {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (w : List E) :
    ContDiff ℝ ∞ (directionalWord w f) := by
  induction w with
  | nil => exact hf
  | cons v w ih =>
    exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem directionalWord_append (v w : List E) (f : E → ℝ) :
    directionalWord (v++w) f = directionalWord v (directionalWord w f) := by
  induction v with
  | nil => rfl
  | cons u v ih => simp only [List.cons_append,directionalWord,ih]

theorem directionalWord_ofFn_eq_iteratedFDeriv {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (v : Fin n → E) (x : E) :
    directionalWord (List.ofFn v) f x = iteratedFDeriv ℝ n f x v := by
  induction n generalizing x with
  | zero => simp [directionalWord]
  | succ n ih =>
    rw [List.ofFn_succ,directionalWord]
    change fderiv ℝ (directionalWord (List.ofFn (Fin.tail v)) f) x (v 0) = _
    rw [funext (fun y => ih (Fin.tail v) y)]
    have hDiff : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := hf.iteratedFDeriv_right (by simp)
    have h := (hDiff.differentiable (by simp) x).iteratedFDeriv_succ_apply_left' (m := v)
    exact h.symm

theorem abs_directionalWord_le_iteratedFDeriv_of_unit {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (w : List E) (x : E) (hUnit : ∀ v ∈ w, ‖v‖ ≤ 1) :
    |directionalWord w f x| ≤ ‖iteratedFDeriv ℝ w.length f x‖ := by
  have h := (iteratedFDeriv ℝ w.length f x).le_opNorm w.get
  rw [← directionalWord_ofFn_eq_iteratedFDeriv hf,List.ofFn_get,Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun v _ => hUnit _ (List.get_mem _ _))))

theorem directionalWord_product_perm {f : (X d) × (X d) → ℝ} (hf : ContDiff ℝ ∞ f)
    {u v : List ((X d) × (X d))} (h : u.Perm v) :
    directionalWord u f = directionalWord v f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [directionalWord,ih]
  | swap a b l => exact productDirection_comm (contDiff_directionalWord hf l) a b
  | trans _ _ hv hw => exact hv.trans hw

theorem directionalWord_productSlice_left {f : (X d) × (X d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (w : List (X d)) (y : (X d)) :
    directionalWord w (fun x => f (x,y)) =
      fun x => directionalWord (w.map (fun v => (v,0))) f (x,y) := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    funext x
    rw [List.map_cons,directionalWord,ih]
    exact fderiv_productSlice_left_apply (contDiff_directionalWord hf _) x y v

theorem directionalWord_productSlice_right {f : (X d) × (X d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (w : List (X d)) (x : (X d)) :
    directionalWord w (fun y => f (x,y)) =
      fun y => directionalWord (w.map (fun v => (0,v))) f (x,y) := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    funext y
    rw [List.map_cons,directionalWord,ih]
    exact fderiv_productSlice_right_apply (contDiff_directionalWord hf _) x y v

theorem harmonic_left_directionalWord_right {f : (X d) × (X d) → ℝ} (hf : ContDiff ℝ ∞ f)
    {g : (MetricField d)} {D V : Set (X d)} (hV : IsOpen V)
    (hLap : ∀ q ∈ D ×ˢ V, laplace g (fun x => f (x,q.2)) q.1 = 0)
    (w : List (X d)) (y : (X d)) (hy : y ∈ V) :
    Harmonic D g (fun x => directionalWord (w.map (fun v => (0,v))) f (x,y)) := by
  induction w generalizing y with
  | nil =>
    exact ⟨(hf.comp (contDiff_id.prodMk contDiff_const)).contDiffOn,fun x hx => hLap (x,y) ⟨hx,hy⟩⟩
  | cons v w ih =>
    exact harmonic_left_productDirection_right (contDiff_directionalWord hf _) hV
      (fun q hq => (ih q.2 hq.2).2 q.1 hq.1) v hy

end CalderonN
