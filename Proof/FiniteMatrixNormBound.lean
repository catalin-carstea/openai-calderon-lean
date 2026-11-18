import Proof.FrameAdjointLinearity
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres

/-- Shared two-index contraction estimate. This is the previously checked
local derivation in the principal tensor bound, extracted for that caller
and the model potential coefficient. -/
lemma norm_weighted_matrix_three_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : I → I → ℝ) (F : I → I → E) (B C : ℝ) (hB : 0 ≤ B)
    (hQ : ∀ i j,|q i j| ≤ B) (hF : ∀ i j,‖F i j‖ ≤ C) :
    ‖∑ i : I,∑ j : I,q i j • F i j‖ ≤ 9*B*C := by
  have hInner (i : I) : ‖∑ j : I,q i j • F i j‖ ≤ 3*B*C :=
    norm_weighted_sum_three_le (q i) (F i) B C hB (hQ i) (hF i)
  have h := norm_weighted_sum_three_le (fun _i : I => (1:ℝ))
    (fun i => ∑ j : I,q i j • F i j) 1 (3*B*C) zero_le_one (fun _i => by norm_num) hInner
  simpa only [one_smul] using h.trans_eq (by ring)
end ShrinkingSpheres
