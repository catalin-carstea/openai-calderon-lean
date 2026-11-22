module

public import Proof.CalderonN.PullbackCoefficientJetBounds
public import Proof.CalderonN.CompactLocalJetBounds

import Proof.CalderonN.UniformCanonicalFrameJets
import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! Uniform higher jets of the pulled-back divergence coefficient on
the compact admissible input locus. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem exists_pullbackDivergenceMatrix_finite_jet_bound (K L : ℝ) (hK : 0 < K) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ q : PullbackCoefficientData dim, ‖q‖ ≤ L → q.1.transpose = q.1 →
      (∀ u : X dim, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => q.1) 0 u u) →
      (∀ u : X dim, ‖u‖ ≤ 2*K*‖q.2 u‖) →
      ContDiffAt ℝ ∞ pullbackDivergenceMatrix q ∧ ∀ n ≤ N, ‖iteratedFDeriv ℝ n pullbackDivergenceMatrix q‖ ≤ B := by
  let P := PullbackCoefficientData dim
  let C : Set P := {q | q.1.transpose = q.1 ∧
      (∀ u, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => q.1) 0 u u) ∧
      (∀ u, ‖u‖ ≤ 2*K*‖q.2 u‖)}
  have hC : IsClosed C := by
    unfold C
    apply IsClosed.inter
    · exact isClosed_eq (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp ((continuous_apply j).comp continuous_fst)) continuous_fst
    · apply IsClosed.inter
      · change IsClosed {q : P | ∀ u, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => q.1) 0 u u}
        rw [show {q : P | ∀ u, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => q.1) 0 u u} =
            ⋂ u : X dim, {q : P | K⁻¹*‖u‖^2 ≤ metricPair (fun _ => q.1) 0 u u} by ext; simp]
        apply isClosed_iInter
        intro u
        exact isClosed_le continuous_const (by
          unfold metricPair
          exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
            (((matrixEntryL i j).continuous.comp (continuous_fst : Continuous (Prod.fst : P → Mat dim))).mul
              (continuous_const (y := u i))).mul (continuous_const (y := u j)))
      · change IsClosed {q : P | ∀ u, ‖u‖ ≤ 2*K*‖q.2 u‖}
        rw [show {q : P | ∀ u, ‖u‖ ≤ 2*K*‖q.2 u‖} =
            ⋂ u : X dim, {q : P | ‖u‖ ≤ 2*K*‖q.2 u‖} by ext; simp]
        apply isClosed_iInter
        intro u
        exact isClosed_le continuous_const
          (continuous_const.mul (((ContinuousLinearMap.apply ℝ (X dim) u).continuous.comp continuous_snd).norm))
  let J := closedBall (0 : P) L ∩ C
  have hJ : IsCompact J := (isCompact_closedBall _ _).inter_right hC
  have hAt (q : P) (hq : q ∈ J) : ContDiffAt ℝ ∞ pullbackDivergenceMatrix q := by
    have hA := ellipticMatrixLocus_posDef hK (R:=L) (A:=q.1)
      (⟨by
        have hqL : ‖q‖ ≤ L := by simpa only [mem_closedBall,dist_zero_right] using hq.1
        simpa only [mem_closedBall,dist_zero_right] using (norm_fst_le q).trans hqL, hq.2.1, hq.2.2.1⟩)
    have hT : Function.Injective q.2 := by
      intro a b h
      have hN := hq.2.2.2 (a-b)
      rw [map_sub,h,sub_self,norm_zero,mul_zero] at hN
      exact sub_eq_zero.mp (norm_le_zero_iff.mp hN)
    exact contDiffAt_pullbackDivergenceMatrix_of_posDef q (pullbackMetricMatrix_posDef hA hT)
  obtain ⟨B,hB,hJet⟩ := exists_uniform_local_finite_jet_bound hJ hAt N
  refine ⟨B,hB,fun q hq hSym hLow hInv => ?_⟩
  have hqJ : q ∈ J := ⟨by simpa only [mem_closedBall,dist_zero_right] using hq,⟨hSym,hLow,hInv⟩⟩
  exact ⟨hAt q hqJ,hJet q hqJ⟩

end CalderonN
