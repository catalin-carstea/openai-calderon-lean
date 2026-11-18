import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace ShrinkingSpheres.SmoothFiniteJetBound
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma apply_const {f : P → E →L[ℝ] F} {p : P} {N : ℕ} {B : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (v : E) :
    SmoothFiniteJetBound (fun x => f x v) p N (B*‖v‖) := by
  refine ⟨mul_nonneg hf.nonneg (norm_nonneg _),hf.smooth.clm_apply contDiffAt_const,?_⟩
  intro n hn
  have hh := norm_iteratedFDeriv_clm_apply_const (c:=v) hf.smooth (n:=n) (by simp)
  exact hh.trans ((mul_le_mul_of_nonneg_left (hf.bound n hn) (norm_nonneg v)).trans_eq (mul_comm _ _))
end ShrinkingSpheres.SmoothFiniteJetBound
