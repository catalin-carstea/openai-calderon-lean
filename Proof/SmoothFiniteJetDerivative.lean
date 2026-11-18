import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace SmoothFiniteJetBound

/-- Differentiating a genuine family consumes one controlled joint jet. -/
lemma fderiv_bound {f : P → E} {p : P} {N : ℕ} {B : ℝ}
    (hf : SmoothFiniteJetBound f p (N+1) B) :
    SmoothFiniteJetBound (fderiv ℝ f) p N B := by
  refine ⟨hf.nonneg,hf.smooth.fderiv_right (m:=∞) (by simp),?_⟩
  intro n hn
  rw [norm_iteratedFDeriv_fderiv]
  exact hf.bound (n+1) (Nat.add_le_add_right hn 1)

/-- The actual evaluation of a smooth operator family on a smooth vector
    field has the same finite-jet bilinear product bound as composition. -/
lemma clm_apply_bound {f : P → E →L[ℝ] F} {g : P → E} {p : P} {N : ℕ} {B C : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (hg : SmoothFiniteJetBound g p N C) :
    SmoothFiniteJetBound (fun x => f x (g x)) p N (2^N*B*C) := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  refine ⟨by positivity,hf.smooth.clm_apply hg.smooth,?_⟩
  intro n hn
  have h := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.id ℝ (E →L[ℝ] F))
    f g p hf.smooth hg.smooth N B C hf.nonneg hg.nonneg hf.bound hg.bound n hn
  exact h.trans (by
    calc
      _ = ‖(ContinuousLinearMap.id ℝ (E →L[ℝ] F))‖*(2^N*B*C) := by ring
      _ ≤ 1*(2^N*B*C) := mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_id_le) (by positivity)
      _ = _ := one_mul _)
end SmoothFiniteJetBound
end ShrinkingSpheres
