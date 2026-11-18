import Proof.ThirdDerivativeProductBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 20
open scoped ContDiff
namespace ShrinkingSpheres

lemma norm_iteratedFDeriv_component_le (f : X → X) (y : X) (i : I)
    (hf : ContDiffAt ℝ ∞ f y) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => f x i) y‖ ≤ ‖iteratedFDeriv ℝ n f y‖ := by
  have hb := (EuclideanSpace.proj (𝕜:=ℝ) i).norm_iteratedFDeriv_comp_left hf (n:=n) (by simp)
  exact hb.trans ((mul_le_mul_of_nonneg_right (norm_euclidean_proj_le_one i) (norm_nonneg _)).trans_eq (one_mul _))

lemma norm_iteratedFDeriv_clm_component_le (J : X → X →L[ℝ] X) (y u : X) (i : I)
    (hJ : ContDiffAt ℝ ∞ J y) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => J x u i) y‖ ≤ ‖u‖*‖iteratedFDeriv ℝ n J y‖ := by
  have hJu : ContDiffAt ℝ ∞ (fun x => J x u) y := hJ.clm_apply contDiffAt_const
  exact (norm_iteratedFDeriv_component_le (fun x => J x u) y i hJu n).trans
    (norm_iteratedFDeriv_clm_apply_const (c:=u) hJ (n:=n) (by simp))

end ShrinkingSpheres
