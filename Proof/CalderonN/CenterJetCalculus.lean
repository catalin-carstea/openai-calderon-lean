module

public import Proof.CalderonN.LocalJetEnvelopeBounds
public import Proof.CalderonN.MatrixFieldJetNorms
public import Mathlib.Analysis.Normed.Operator.Prod

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Pointwise jet bounds for the coordinate maps used in the actual moving-center
derivative. Only jets of the explicit affine frame path need uniform bounds. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {P E F G : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma norm_iteratedFDeriv_bilinear_envelope_at (L : E →L[ℝ] F →L[ℝ] G)
    (f : P → E) (g : P → F) (x : P) (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hF : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hG : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => L (f y) (g y)) x‖ ≤ (2:ℝ)^n*‖L‖*A*B := by
  obtain ⟨u,hu,hfu⟩ := hf.contDiffOn (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨v,hv,hgv⟩ := hg.contDiffOn (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨U,hUu,hU,hxU⟩ := mem_nhds_iff.mp hu
  obtain ⟨V,hVv,hV,hxV⟩ := mem_nhds_iff.mp hv
  let S := U ∩ V
  have hS : IsOpen S := hU.inter hV
  have hxS : x ∈ S := ⟨hxU,hxV⟩
  have hlf : ContDiffOn ℝ (n:ℕ∞ω) (L ∘ f) S := L.contDiff.contDiffOn.comp
    (hfu.mono (fun y hy => hUu hy.1)) (mapsTo_univ _ _)
  have hb := norm_iteratedFDerivWithin_clm_apply hlf
    (hgv.mono (fun y hy => hVv hy.2)) hS.uniqueDiffOn hxS (n:=n) (N:=(n:ℕ∞ω)) le_rfl
  have hEq (h : P → F) (i : ℕ) :=
    iteratedFDerivWithin_of_isOpen (𝕜:=ℝ) (f:=h) i hS hxS
  rw [iteratedFDerivWithin_of_isOpen n hS hxS] at hb
  refine hb.trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*(‖L‖*A)*B := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [iteratedFDerivWithin_of_isOpen i hS hxS,hEq]
      have hLeft := L.norm_iteratedFDeriv_comp_left (hf.of_le (by simp : (i:ℕ∞ω) ≤ ∞))
        (n:=i) le_rfl
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (hLeft.trans (mul_le_mul_of_nonneg_left (hF i hin) (norm_nonneg _))) (by positivity))
        (hG (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      have hSum : (∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)) = (2:ℝ)^n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [hSum]
      ring

lemma norm_iteratedFDeriv_prod_envelope_at (f : P → E) (g : P → F) (x : P) (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) {A B : ℝ}
    (hF : ‖iteratedFDeriv ℝ n f x‖ ≤ A) (hG : ‖iteratedFDeriv ℝ n g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => (f y,g y)) x‖ ≤ max A B := by
  rw [iteratedFDeriv_prodMk (hf.of_le (by simp : (n:ℕ∞ω) ≤ ∞))
    (hg.of_le (by simp : (n:ℕ∞ω) ≤ ∞)) le_rfl,ContinuousMultilinearMap.opNorm_prod]
  exact max_le_max hF hG

lemma norm_iteratedFDeriv_affine_envelope_at (L : P →L[ℝ] E) (b : E) (x : P) (n : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (h₀ : ‖b+L x‖ ≤ A) (h₁ : ‖L‖ ≤ A) :
    ‖iteratedFDeriv ℝ n (fun y => b+L y) x‖ ≤ A := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero] using h₀
  | succ n =>
    have hD : fderiv ℝ (fun y => b+L y) = fun _ : P => L :=
      funext fun y => (L.hasFDerivAt.const_add b).fderiv
    rw [← norm_iteratedFDeriv_fderiv,hD]
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using h₁
    | succ n => simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using hA

lemma norm_iteratedFDeriv_matrix_le_of_entries {dim : ℕ}
    (f : P → Mat dim) (x : P) (n : ℕ) (hf : ContDiffAt ℝ ∞ f x) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i j, ‖iteratedFDeriv ℝ n (fun y => f y i j) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply (Matrix.norm_le_iff (mul_nonneg hC (Finset.prod_nonneg (fun k _ => norm_nonneg (v k))))).2
  intro i j
  have hEntry := (matrixEntryL i j).iteratedFDeriv_comp_left
    (hf.of_le (by simp : (n:ℕ∞ω) ≤ ∞)) (n:=n) le_rfl
  have hEval := congrArg (fun T : (P [×n]→L[ℝ] ℝ) => T v) hEntry
  change (iteratedFDeriv ℝ n (fun y => f y i j) x) v = (iteratedFDeriv ℝ n f x v) i j at hEval
  rw [← hEval]
  exact (ContinuousMultilinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (h i j) (Finset.prod_nonneg fun k _ => norm_nonneg (v k)))

end CalderonN
