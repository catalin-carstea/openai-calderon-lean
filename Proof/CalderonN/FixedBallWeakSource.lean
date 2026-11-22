module

public import Proof.CalderonN.FixedBallSourceEnergy
import Mathlib.Tactic

public section

/- Existence for the same zero-trace variational problem as the released
   FixedBallClassicalSource, with its general-dimensional volume gain. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Matrix.Norms.Elementwise

namespace CalderonN

variable {n : ℕ}

local instance : TopologicalSpace.PseudoMetrizableSpace (Mat n) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (I n → I n → ℝ))

set_option maxHeartbeats 1800000 in
theorem exists_fixedBall_weak_source_gradient (hn : 3 ≤ n)
    {a : X n → Mat n} (ha : Continuous a) {lo hi : ℝ}
    (he : TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) a lo hi) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Lp ℝ 2 (volume.restrict (fixedBallOpens n))) (A : Set (X n)),
        MeasurableSet A →
        (∀ᵐ x ∂(volume.restrict (fixedBallOpens n)), x ∉ A → F x = 0) →
        ∃ u : FixedBallH1Zero n,
          TauCeti.PDE.IsWeakSolutionDirichlet a 0 0 F u ∧
          ‖TauCeti.W1p.gradient (u : FixedBallH1 n)‖ ≤
            C * ((volume.restrict (fixedBallOpens n)).real A) ^ (1 / (n : ℝ)) * ‖F‖ ∧
          MemLp (TauCeti.W1p.value (u : FixedBallH1 n) : X n → ℝ) (criticalSobolevExponent n)
            (volume.restrict (fixedBallOpens n)) ∧
          (eLpNorm (TauCeti.W1p.value (u : FixedBallH1 n) : X n → ℝ) (criticalSobolevExponent n)
            (volume.restrict (fixedBallOpens n))).toReal ≤
            C * ((volume.restrict (fixedBallOpens n)).real A) ^ (1 / (n : ℝ)) * ‖F‖ := by
  obtain ⟨C,hC,hG⟩ := exists_fixedBall_source_gradient_bound hn ha he
  obtain ⟨S,hS,hSob⟩ := fixedBall_zeroTrace_critical_bound hn
  refine ⟨max C (S*C), hC.trans_le (le_max_left _ _), fun F A hA hSupp => ?_⟩
  have hsolve : ∃ u : FixedBallH1Zero n, TauCeti.PDE.IsWeakSolutionDirichlet a 0 0 F u := by
    cases n with
    | zero => omega
    | succ k =>
      let b : X (k+1) → X (k+1) := 0
      let c : X (k+1) → ℝ := 0
      let μ := (volume : Measure (X (k+1))).restrict (fixedBallOpens (k+1))
      have hb : AEStronglyMeasurable b μ := aestronglyMeasurable_const
      have hc : AEStronglyMeasurable c μ := aestronglyMeasurable_const
      have hsmall : (0 : ℝ) * (2 * 1) < lo := by simpa using he.1
      have hB : (fixedBallOpens (k+1) : Set (X (k+1))) ⊆ ball 0 (1:ℝ) := Subset.rfl
      obtain ⟨u,hu,_⟩ := he.existsUnique_isWeakSolutionDirichlet_of_subset_ball
        (b := b) (c := c) (beta := 0) (gamma := 0)
        ha.aestronglyMeasurable hb hc le_rfl (by simp [b]) (by simp [c]) (by simp [c])
        zero_le_one hB hsmall F
      exact ⟨u,hu⟩
  obtain ⟨u,hu⟩ := hsolve
  have hG' := hG F u hu A hA hSupp
  have hν : 0 ≤ ((volume.restrict (fixedBallOpens n)).real A) ^ (1 / (n : ℝ)) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  refine ⟨u, hu, hG'.trans ?_, (hSob u).1, (hSob u).2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hν) (norm_nonneg _)
  · refine (mul_le_mul_of_nonneg_left hG' hS.le).trans ?_
    rw [← mul_assoc S, ← mul_assoc S]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hν) (norm_nonneg _)

end CalderonN
