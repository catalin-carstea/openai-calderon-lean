module

public import Proof.CalderonN.BallRegularity.StrongOperatorForcing
public import Proof.CalderonN.MatrixFieldJetNorms

import Proof.CalderonN.CompactFiniteJets
import Proof.CalderonN.LocalHigherDerivativeBounds
import Proof.CalderonN.EllipticCalculus
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 2700000
set_option maxSynthPendingDepth 20

namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

theorem norm_compactCoefficient_le (s : ℕ) {u : X dim → ℝ} (hu : ContDiff ℝ ∞ u)
    (hcu : HasCompactSupport u) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x, ∀ k ≤ s, ‖iteratedFDeriv ℝ k u x‖ ≤ B) :
    ‖compactCoefficient s u hu hcu‖ ≤ B := by
  change ‖compactCoefficientJet s u hu hcu‖ ≤ B
  change ‖(compactCoefficientJet s u hu hcu :
    (j : Fin (s+1)) → BoundedContinuousFunction (X dim) ((X dim) [×j.val]→L[ℝ] ℝ))‖ ≤ B
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro j
  apply (BoundedContinuousFunction.norm_le hB).2
  intro x
  rw [compactCoefficientJet_apply]
  exact h x j.val (Nat.le_of_lt_succ j.isLt)

/-- A fixed cutoff preserves exact germs on the unit ball and transfers
a local finite jet bound to the native coefficient norm. -/
theorem exists_uniform_cutoffCoefficientLifts (dim : ℕ) [NeZero dim] :
    ∃ C ≥ (0 : ℝ), ∀ (a : X dim → Mat dim) (B : ℝ), 0 ≤ B →
      (∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) (ball (0 : X dim) 2)) →
      (∀ i j, ∀ z ∈ ball (0 : X dim) 2, ∀ k ≤ 2,
        ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ B) →
      ∃ F : SmoothCoefficientMatrix dim 2, ‖F‖ ≤ C*B ∧
        EqOn (coefficientMatrixField 2 F) a (ball (0 : X dim) (5/4)) := by
  let χ : ContDiffBump (0 : X dim) := ⟨5/4,3/2,by norm_num,by norm_num⟩
  let f : X dim → ℝ := χ
  have hf : ContDiff ℝ ∞ f := χ.contDiff
  let U := ball (0 : X dim) 2
  have hU : IsOpen U := isOpen_ball
  have hSupp : tsupport f ⊆ U := χ.tsupport_eq ▸ closedBall_subset_ball (by norm_num)
  have hχ : EqOn f (fun _ => (1:ℝ)) (ball (0 : X dim) (5/4)) :=
    fun _ hx => χ.one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨Q,hQ,hQjet⟩ := exists_uniform_finite_jet_bound (isCompact_closedBall (0 : X dim) 2) hf 2
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  refine ⟨4*Q,by positivity,?_⟩
  intro a B hB ha hJet
  let w (i j : I dim) (z : X dim) := f z * a z i j
  have hw (i j : I dim) : ContDiff ℝ ∞ (w i j) :=
    Elliptic.contDiff_mul_of_tsupport_subset hU hf hSupp (ha i j)
  have hwc (i j : I dim) : HasCompactSupport (w i j) := χ.hasCompactSupport.mul_right
  let F : SmoothCoefficientMatrix dim 2 := fun i j => compactCoefficient 2 (w i j) (hw i j) (hwc i j)
  have hF (i j : I dim) : ‖F i j‖ ≤ (4*Q)*B := by
    apply norm_compactCoefficient_le _ _ _ (by positivity)
    intro z k hk
    by_cases hz : z ∈ U
    · have hb := norm_iteratedFDeriv_mul_at hU hf.contDiffOn (ha i j) hz k
      calc
        _ ≤ ∑ t ∈ Finset.range (k+1), (k.choose t : ℝ) *
            ‖iteratedFDeriv ℝ t f z‖ * ‖iteratedFDeriv ℝ (k-t) (fun z => a z i j) z‖ := hb
        _ ≤ ∑ t ∈ Finset.range (k+1), (k.choose t : ℝ)*(Q*B) := by
          apply Finset.sum_le_sum
          intro t ht
          have ht' := Finset.mem_range.mp ht
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul
            (hQjet z (ball_subset_closedBall hz) t (by omega)) (hJet i j z hz _ (by omega))
            (norm_nonneg _) hQ₀) (by positivity)
        _ = (2:ℝ)^k*(Q*B) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose k
        _ ≤ (4*Q)*B := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (by
            simpa only [show (2:ℝ)^2 = 4 by norm_num] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk)
            (mul_nonneg hQ₀ hB)
    · have he : w i j =ᶠ[𝓝 z] 0 := by
        have hF₀ : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hSupp h))
        filter_upwards [hF₀] with q hq
        change f q * a q i j = 0
        rw [show f q = 0 from hq,zero_mul]
      rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
      change ‖iteratedFDeriv ℝ k (fun _ : X dim => (0 : ℝ)) z‖ ≤ _
      simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
      positivity
  refine ⟨F,(pi_norm_le_iff_of_nonneg (by positivity)).2
    (fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 (hF i)),?_⟩
  intro z hz
  ext i j
  change coefficientValue 2 (F i j) z = a z i j
  rw [show F i j = compactCoefficient 2 (w i j) (hw i j) (hwc i j) from rfl,coefficientValue_compactCoefficient]
  change f z * a z i j = _
  rw [show f z = 1 from hχ hz,one_mul]

end CalderonN.BallDirichlet
