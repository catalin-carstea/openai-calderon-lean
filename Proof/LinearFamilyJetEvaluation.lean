import Proof.BilinearFamilyJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P Q V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Uniform bounds on every fixed input control the jet in operator norm.
    Evaluation commutes with parameter differentiation before taking norms. -/
theorem norm_iteratedFDeriv_linear_family_of_apply_le
    (L : P → Q →L[ℝ] V) (x : P) (hL : ContDiffAt ℝ ∞ L x)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hApply : ∀ q : Q,‖iteratedFDeriv ℝ n (fun p => L p q) x‖ ≤ C*‖q‖) :
    ‖iteratedFDeriv ℝ n L x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  intro q
  let ev : (Q →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V q
  have he := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => P) V => A v)
    (ev.iteratedFDeriv_comp_left hL (i:=n) (by simp))
  change iteratedFDeriv ℝ n (fun p => L p q) x v = (iteratedFDeriv ℝ n L x v) q at he
  rw [← he]
  exact ((iteratedFDeriv ℝ n (fun p => L p q) x).le_opNorm v).trans
    ((mul_le_mul_of_nonneg_right (hApply q) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))).trans_eq (by ring))

/-- A gained operator-family jet applied to a moving input keeps its gain;
    fixed-input estimates alone are promoted to operator jets first. -/
theorem norm_iteratedFDeriv_moving_linear_family_le
    (L : P → Q →L[ℝ] V) (q : P → Q) (x : P)
    (hL : ContDiffAt ℝ ∞ L x) (hq : ContDiffAt ℝ ∞ q x)
    (N : ℕ) (r C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hFixed : ∀ n : ℕ,n ≤ N → ∀ u : Q,‖iteratedFDeriv ℝ n (fun p => L p u) x‖ ≤ C*‖u‖*r^2)
    (hqJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n q x‖ ≤ B)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => L p (q p)) x‖ ≤ (2^N*C*B)*r^2 := by
  have hLJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j L x‖ ≤ C*r^2 :=
    norm_iteratedFDeriv_linear_family_of_apply_le L x hL j (C*r^2) (by positivity)
      (fun u => (hFixed j hj u).trans_eq (by ring))
  let ev : Q →L[ℝ] (Q →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V
  have hEv : ‖ev‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro A
    exact (A.le_opNorm u).trans_eq (by ring)
  have h := norm_iteratedFDeriv_bilinear_common_bound ev q L x hq hL N B (C*r^2)
    hB (by positivity) hqJets hLJets n hn
  exact h.trans (by
    calc
      _ = ‖ev‖*((2^N*C*B)*r^2) := by ring
      _ ≤ 1*((2^N*C*B)*r^2) := mul_le_mul_of_nonneg_right hEv (by positivity)
      _ = _ := one_mul _)

end ShrinkingSpheres
