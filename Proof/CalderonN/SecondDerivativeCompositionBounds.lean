module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Adapted from the checked Proposition 5.3 release. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 20
open Filter
open scoped ContDiff Topology
namespace CalderonN
variable {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]

lemma second_fderiv_comp_at (f : P → Q) (g : Q → R) (x a b : P)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x a b =
      fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x a b)+
        fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) := by
  have hdf := (hf.differentiableAt (by simp)).hasFDerivAt
  have hDg := ((hg.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp x hdf
  have hDf := ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hProduct := hDg.clm_comp hDf
  simp only [Function.comp_def] at hProduct
  have hEq : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x] (fun y => (fderiv ℝ g (f y)).comp (fderiv ℝ f y)) := by
    have hfn := (hf.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)
    have hgn := (hf.continuousAt.eventually ((hg.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)))
    filter_upwards [hfn,hgn] with y hfy hgy
    exact fderiv_comp y (hgy.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))
  rw [hEq.fderiv_eq,hProduct.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]

lemma norm_second_fderiv_comp_at (f : P → Q) (g : Q → R) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) :
    ‖fderiv ℝ (fderiv ℝ (g ∘ f)) x‖ ≤
      ‖fderiv ℝ g (f x)‖*‖fderiv ℝ (fderiv ℝ f) x‖+
        ‖fderiv ℝ (fderiv ℝ g) (f x)‖*‖fderiv ℝ f x‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro a b
  rw [second_fderiv_comp_at f g x a b hf hg]
  have h1 : ‖fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x a b)‖ ≤
      ‖fderiv ℝ g (f x)‖*‖fderiv ℝ (fderiv ℝ f) x‖*‖a‖*‖b‖ := by
    calc
      _ ≤ ‖fderiv ℝ g (f x)‖*‖fderiv ℝ (fderiv ℝ f) x a b‖ := (fderiv ℝ g (f x)).le_opNorm _
      _ ≤ ‖fderiv ℝ g (f x)‖*(‖fderiv ℝ (fderiv ℝ f) x‖*‖a‖*‖b‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm₂ _ _ _
      _ = _ := by ring
  have h2 : ‖fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x a) (fderiv ℝ f x b)‖ ≤
      ‖fderiv ℝ (fderiv ℝ g) (f x)‖*‖fderiv ℝ f x‖^2*‖a‖*‖b‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ g) (f x)‖*‖fderiv ℝ f x a‖*‖fderiv ℝ f x b‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ g) (f x)‖*(‖fderiv ℝ f x‖*‖a‖)*(‖fderiv ℝ f x‖*‖b‖) := by
        gcongr
        · exact (fderiv ℝ f x).le_opNorm a
        · exact (fderiv ℝ f x).le_opNorm b
      _ = _ := by ring
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end CalderonN
