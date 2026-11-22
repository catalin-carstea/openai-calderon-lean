module

public import Proof.CalderonN.CenterJetCalculus

import Proof.CalderonN.SecondDerivativeCompositionBounds
import Proof.CalderonN.CurveAffineError
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Recover a quadratic spatial Taylor estimate for a center derivative
from the mixed jets of a locally smooth coefficient. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def centerDerivativeSlice (F : ℝ × P → E) (v : P) : E :=
  fderiv ℝ F (0,v) (1,0)

lemma hasDerivAt_centerDerivativeSlice (F : ℝ × P → E) (v : P) (t : ℝ)
    (h : DifferentiableAt ℝ F (t,v)) :
    HasDerivAt (fun s => F (s,v)) (fderiv ℝ F (t,v) (1,0)) t := by
  have hP : HasDerivAt (fun s : ℝ => (s,v)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t v)
  exact h.hasFDerivAt.comp_hasDerivAt t hP

theorem centerDerivativeSlice_first_bound (F : ℝ × P → E) (v : P)
    (hF : ContDiffAt ℝ ∞ F (0,v)) {B : ℝ} (hB : 0 ≤ B)
    (h₂ : ‖iteratedFDeriv ℝ 2 F (0,v)‖ ≤ B) :
    ‖fderiv ℝ (centerDerivativeSlice F) v‖ ≤ B := by
  let J := ContinuousLinearMap.inr ℝ ℝ P
  let G (p : ℝ × P) := fderiv ℝ F p (1,0)
  have hDf := hF.fderiv_right (m:=∞) (by simp)
  have hG : ContDiffAt ℝ ∞ G (0,v) := hDf.clm_apply contDiffAt_const
  have h := norm_iteratedFDeriv_clm_apply_const (c:=((1 : ℝ),(0:P))) hDf (n:=1) (by simp)
  rw [norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_one] at h
  have hG₁ : ‖fderiv ℝ G (J v)‖ ≤ B := by
    change ‖fderiv ℝ G (0,v)‖ ≤ B
    exact (by simpa [G,Prod.norm_mk] using h : ‖fderiv ℝ G (0,v)‖ ≤
      ‖iteratedFDeriv ℝ 2 F (0,v)‖).trans h₂
  have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]
    change ‖((0:ℝ),w)‖ ≤ ‖w‖
    simp [Prod.norm_mk,norm_nonneg]
  change ‖fderiv ℝ (G ∘ J) v‖ ≤ B
  have hG' : DifferentiableAt ℝ G (J v) := hG.differentiableAt (by simp)
  have hD : HasFDerivAt (G ∘ J) ((fderiv ℝ G (J v)).comp J) v :=
    hG'.hasFDerivAt.comp v J.hasFDerivAt
  rw [hD.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hG₁ hJ (norm_nonneg _) hB).trans_eq (mul_one _))

theorem centerDerivativeSlice_smooth_second_bound (F : ℝ × P → E) (v : P)
    (hF : ContDiffAt ℝ ∞ F (0,v)) {B : ℝ} (hB : 0 ≤ B)
    (h₃ : ‖iteratedFDeriv ℝ 3 F (0,v)‖ ≤ B) :
    ContDiffAt ℝ ∞ (centerDerivativeSlice F) v ∧
    ‖fderiv ℝ (fderiv ℝ (centerDerivativeSlice F)) v‖ ≤ B := by
  let J := ContinuousLinearMap.inr ℝ ℝ P
  let G (p : ℝ × P) := fderiv ℝ F p (1,0)
  have hDf := hF.fderiv_right (m:=∞) (by simp)
  have hG : ContDiffAt ℝ ∞ G (0,v) := hDf.clm_apply contDiffAt_const
  have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]
    change ‖((0:ℝ),w)‖ ≤ ‖w‖
    simp [Prod.norm_mk,norm_nonneg]
  have hG₂ := norm_iteratedFDeriv_clm_apply_const (c:=((1 : ℝ),(0:P))) hDf (n:=2) (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hG₂
  have h₂ : ‖fderiv ℝ (fderiv ℝ G) (J v)‖ ≤ B := by
    change ‖fderiv ℝ (fderiv ℝ G) (0,v)‖ ≤ B
    have hn : ‖iteratedFDeriv ℝ 2 G (0,v)‖ = ‖fderiv ℝ (fderiv ℝ G) (0,v)‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one]
    rw [← hn]
    exact (by simpa [G,Prod.norm_mk] using hG₂ : ‖iteratedFDeriv ℝ 2 G (0,v)‖ ≤
      ‖iteratedFDeriv ℝ 3 F (0,v)‖).trans h₃
  change ContDiffAt ℝ ∞ (G ∘ J) v ∧ ‖fderiv ℝ (fderiv ℝ (G ∘ J)) v‖ ≤ B
  refine ⟨hG.comp v J.contDiff.contDiffAt,?_⟩
  have h := norm_second_fderiv_comp_at J G v J.contDiff.contDiffAt hG
  have hDeriv : fderiv ℝ (⇑J) = fun _ => J := funext fun _ => J.fderiv
  simp only [hDeriv,fderiv_fun_const,Pi.zero_apply,norm_zero,mul_zero,zero_add] at h
  exact h.trans ((mul_le_mul h₂ (pow_le_pow_left₀ (norm_nonneg _) hJ 2) (sq_nonneg _) hB).trans_eq
    (by ring))

/-- The estimates require control only along the straight segment, so the
chosen larger ball need not support a global continuation of the coefficient. -/
theorem norm_taylor_remainder_of_second_bound (C : P → E) (w : P) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ C (t • w) ∧
      ‖fderiv ℝ (fderiv ℝ C) (t • w)‖ ≤ B) :
    ‖C w-C 0-fderiv ℝ C 0 w‖ ≤ B*‖w‖^2 ∧
      ‖fderiv ℝ C w-fderiv ℝ C 0‖ ≤ B*‖w‖ := by
  let D := fderiv ℝ C
  have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one,le_rfl⟩
  have hRay (t : ℝ) : HasDerivAt (fun s : ℝ => s • w) w t := by
    simpa only [id_eq,one_smul] using (hasDerivAt_id t).smul_const w
  have hDT (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u : ℝ => D (u • w)) (fderiv ℝ D (t • w) w) t :=
    ((((h t ht).1.fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hRay t))
  have hDerr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖D (t • w)-D 0‖ ≤ (B*‖w‖)*t := by
    have he := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hDT s hs).differentiableAt) (fun s hs => by
        rw [(hDT s hs).deriv]
        exact ((fderiv ℝ D (s • w)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (h s hs).2 (norm_nonneg w))) h0 ht
    simpa only [zero_smul,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using he
  let G (t : ℝ) := C (t • w)
  let F (t : ℝ) := D (t • w) w
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt G (F t) t :=
    ((h t ht).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hRay t)
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖F t-D 0 w‖ ≤ (B*‖w‖^2)*t := by
    change ‖(D (t • w)-D 0) w‖ ≤ _
    exact ((D (t • w)-D 0).le_opNorm w).trans
      ((mul_le_mul_of_nonneg_right (hDerr t ht) (norm_nonneg w)).trans_eq (by ring))
  refine ⟨?_,by simpa only [one_smul,mul_one] using hDerr 1 h1⟩
  simpa only [G,one_smul,one_pow,mul_one] using norm_curve_affine_error_le
    G F (C 0) (D 0 w) (B*‖w‖^2) 1 (by positivity) h1 hG (by simp [G]) hF

end CalderonN
