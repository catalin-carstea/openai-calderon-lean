module

public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Adapted from `CurveAffineError` in the checked Proposition 5.3 release. -/

public section

noncomputable section
set_option autoImplicit false
open Set
namespace CalderonN

/-- A derivative error vanishing linearly at the initial time gives a quadratic
    affine-position error. No global extension or integral representation is needed. -/
theorem norm_curve_affine_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F V : ℝ → E) (a b : E) (B t : ℝ) (hB : 0 ≤ B) (ht : t ∈ Icc (0:ℝ) 1)
    (hF : ∀ s ∈ Icc (0:ℝ) 1,HasDerivAt F (V s) s) (hZero : F 0 = a)
    (hV : ∀ s ∈ Icc (0:ℝ) 1,‖V s-b‖ ≤ B*s) :
    ‖F t-a-t • b‖ ≤ B*t^2 := by
  let G : ℝ → E := fun s => F s-s • b
  have hSub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) 1 := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hGD (s : ℝ) (hs : s ∈ Icc (0:ℝ) t) : HasDerivAt G (V s-b) s := by
    have hScale : HasDerivAt (fun q : ℝ => q • b) b s := by
      convert (hasDerivAt_id s).smul_const b using 1 <;> simp only [Function.id_def,one_smul]
    exact (hF s (hSub hs)).sub hScale
  have hBound (s : ℝ) (hs : s ∈ Icc (0:ℝ) t) : ‖deriv G s‖ ≤ B*t := by
    rw [(hGD s hs).deriv]
    exact (hV s (hSub hs)).trans (mul_le_mul_of_nonneg_left hs.2 hB)
  have hb := (convex_Icc (0:ℝ) t).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hGD s hs).differentiableAt) hBound ⟨le_rfl,ht.1⟩ ⟨ht.1,le_rfl⟩
  have hEq : F t-a-t • b = G t-G 0 := by
    dsimp [G];rw [hZero,zero_smul];abel
  rw [hEq]
  convert hb using 1 <;> simp only [sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] <;> ring

end CalderonN
