import Proof.RadialTaylorHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordered differentiation along independently specified vector fields. -/
def orderedDirectionalFamily (V : ℕ → P → P) (F : P → E) : ℕ → P → E
  | 0 => F
  | n+1 => fun p => fderiv ℝ (orderedDirectionalFamily V F n) p (V n p)

theorem contDiffAt_orderedDirectionalFamily (V : ℕ → P → P) (F : P → E) (p : P)
    (hF : ContDiffAt ℝ ∞ F p) (hV : ∀ n,ContDiffAt ℝ ∞ (V n) p) (n : ℕ) :
    ContDiffAt ℝ ∞ (orderedDirectionalFamily V F n) p := by
  induction n with
  | zero => exact hF
  | succ n ih => exact (ih.fderiv_right (m:=∞) (by simp)).clm_apply (hV n)

/-- All mixed jets of ordered directional derivatives follow from ordinary
    joint jets and the actual vector-field jets. A gained factor in C is
    preserved, rather than differentiated as an independent budget. -/
theorem norm_iteratedFDeriv_orderedDirectionalFamily_le
    (V : ℕ → P → P) (F : P → E) (p : P)
    (hF : ContDiffAt ℝ ∞ F p) (hV : ∀ n,ContDiffAt ℝ ∞ (V n) p)
    (N : ℕ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hFJets : ∀ k : ℕ,k ≤ N → ‖iteratedFDeriv ℝ k F p‖ ≤ C)
    (hVJets : ∀ n : ℕ,n < N → ∀ k : ℕ,k+1 ≤ N → ‖iteratedFDeriv ℝ k (V n) p‖ ≤ D) :
    ∀ n k : ℕ,n+k ≤ N →
      ‖iteratedFDeriv ℝ k (orderedDirectionalFamily V F n) p‖ ≤ (2^N*D)^n*C := by
  intro n
  induction n with
  | zero => intro k hk;simpa only [orderedDirectionalFamily,pow_zero,one_mul] using hFJets k (by omega)
  | succ n ih =>
    intro k hk
    have hn : n < N := by omega
    have hSmooth := contDiffAt_orderedDirectionalFamily V F p hF hV n
    have hDF : ContDiffAt ℝ ∞ (fderiv ℝ (orderedDirectionalFamily V F n)) p :=
      hSmooth.fderiv_right (m:=∞) (by simp)
    have hJets (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j (fderiv ℝ (orderedDirectionalFamily V F n)) p‖ ≤ (2^N*D)^n*C := by
      rw [norm_iteratedFDeriv_fderiv]
      exact ih (j+1) (by omega)
    let ev : P →L[ℝ] (P →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E
    have hev : ‖ev‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro u
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro A
      exact (A.le_opNorm u).trans_eq (by ring)
    have hh := norm_iteratedFDeriv_bilinear_common_bound ev (V n) (fderiv ℝ (orderedDirectionalFamily V F n)) p
      (hV n) hDF k D ((2^N*D)^n*C) hD (by positivity)
      (fun j hj => hVJets n hn j (by omega)) hJets k le_rfl
    change ‖iteratedFDeriv ℝ k (orderedDirectionalFamily V F (n+1)) p‖ ≤ _ at hh
    calc
      _ ≤ ‖ev‖*2^k*D*((2^N*D)^n*C) := hh
      _ ≤ 1*2^N*D*((2^N*D)^n*C) := by gcongr <;> norm_num <;> omega
      _ = (2^N*D)^(n+1)*C := by ring

end ShrinkingSpheres
