module

public import Proof.CalderonN.SmoothMetricFrame
public import Proof.CalderonN.Coercivity

import Proof.CalderonN.CenterJetCalculus
import Proof.CalderonN.LocalJetEnvelopeBounds
import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! A fixed coordinate Gram–Schmidt trivialization has uniform base
derivative bounds from the admitted reference-metric jets. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN
variable {dim : ℕ} [NeZero dim]

@[expose] def ellipticMatrixLocus (dim : ℕ) (K R : ℝ) : Set (Mat dim) :=
  closedBall 0 R ∩ {A | A.transpose = A ∧
    ∀ u : X dim, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => A) 0 u u}

theorem isCompact_ellipticMatrixLocus (dim : ℕ) (K R : ℝ) :
    IsCompact (ellipticMatrixLocus dim K R) := by
  have hS : IsClosed {A : Mat dim | A.transpose = A ∧
      ∀ u : X dim, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => A) 0 u u} := by
    apply IsClosed.inter
    · have h : Continuous (fun A : Mat dim => A.transpose) :=
        continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j)
      exact isClosed_eq h continuous_id
    · change IsClosed {A : Mat dim | ∀ u : X dim, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => A) 0 u u}
      rw [show {A : Mat dim | ∀ u : X dim, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => A) 0 u u} =
          ⋂ u : X dim, {A : Mat dim | K⁻¹*‖u‖^2 ≤ metricPair (fun _ => A) 0 u u} by ext; simp]
      apply isClosed_iInter
      intro u
      exact isClosed_le continuous_const (by
        unfold metricPair
        exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
          (((matrixEntryL i j).continuous.mul (continuous_const (y := u i))).mul (continuous_const (y := u j))))
  exact (isCompact_closedBall (0 : Mat dim) R).inter_right hS

theorem ellipticMatrixLocus_posDef {K R : ℝ} (hK : 0 < K) {A : Mat dim}
    (hA : A ∈ ellipticMatrixLocus dim K R) : A.PosDef := by
    have hAS := hA.2
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hAS.1) ?_
    intro u hu
    let w : X dim := WithLp.toLp 2 u
    have hw : w ≠ 0 := fun h => hu (congrArg WithLp.ofLp h)
    have h := (mul_pos (inv_pos.mpr hK) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))).trans_le (hAS.2 w)
    simpa only [metricPair,w,Matrix.mulVec,dotProduct,Finset.mul_sum,star_trivial,mul_assoc,mul_left_comm] using h

private theorem exists_smoothMetricFrame_matrix_jet_envelope (K R : ℝ) (hK : 0 < K) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : Mat dim, ‖A‖ ≤ R → A.transpose = A →
      (∀ u : X dim, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => A) 0 u u) →
      ∀ i : I dim, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun B => smoothMetricFrame B i) A‖ ≤ C := by
  let J := ellipticMatrixLocus dim K R
  have hJ := isCompact_ellipticMatrixLocus dim K R
  have hPos (A : Mat dim) (hA : A ∈ J) : A.PosDef := ellipticMatrixLocus_posDef hK hA
  have hCont (i : I dim) (j : Fin (m+1)) :
      ContinuousOn (iteratedFDeriv ℝ j.val (fun A : Mat dim => smoothMetricFrame A i)) J :=
    fun A hA => ((contDiffAt_smoothMetricFrame (hPos A hA) i).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
  choose D hD using fun i (j : Fin (m+1)) => hJ.exists_bound_of_continuousOn (hCont i j)
  let C : ℝ := 1+∑ i,∑ j, |D i j|
  refine ⟨C,le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _),?_⟩
  intro A hA hSym hLow i j hj
  have hAJ : A ∈ J := ⟨by simpa only [mem_closedBall,dist_zero_right] using hA,⟨hSym,hLow⟩⟩
  let k : Fin (m+1) := ⟨j,by omega⟩
  refine (hD i k A hAJ).trans ((le_abs_self _).trans ?_)
  have hSingle := (Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ k)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (D a b))) (Finset.mem_univ i))
  exact hSingle.trans (le_add_of_nonneg_left (by norm_num))

theorem uniform_canonical_metric_frame_jets (K : ℝ) (hK : 0 < K) {m : ℕ} (M : Fin (m+1) → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Set (X dim)} {g : MetricField dim}, IsOpen Ω →
      Elliptic Ω K g →
      (∀ (j : Fin (m+1)) i k, ∀ y ∈ Ω, ‖iteratedFDeriv ℝ j.val (fun x => g x i k) y‖ ≤ M j) →
      ∀ y ∈ Ω, ∀ i : I dim, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (fun x => smoothMetricFrame (g x) i) y‖ ≤ C := by
  let R : ℝ := 1 + ∑ j, |M j|
  have hR : 1 ≤ R := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hMR (j : Fin (m+1)) : M j ≤ R :=
    (le_abs_self _).trans ((Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1)))
  obtain ⟨C,hC,hFrame⟩ := exists_smoothMetricFrame_matrix_jet_envelope (dim:=dim) K R hK m
  have hFac : (1:ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
  refine ⟨m.factorial*C*R^m,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hFac hC) (one_le_pow₀ hR),?_⟩
  intro Ω g hΩ hg hJets y hy i j hj
  have hG : ContDiffAt ℝ ∞ g y :=
    (contDiffOn_pi.mpr (fun a => contDiffOn_pi.mpr (fun b => hg.1 a b))).contDiffAt (hΩ.mem_nhds hy)
  have hNorm (k : ℕ) (hk : k ≤ m) : ‖iteratedFDeriv ℝ k g y‖ ≤ R := by
    apply norm_iteratedFDeriv_matrix_le_of_entries g y k hG (zero_le_one.trans hR)
    intro a b
    exact (hJets ⟨k,by omega⟩ a b y hy).trans (hMR _)
  have h0 : ‖g y‖ ≤ R := by simpa only [norm_iteratedFDeriv_zero] using hNorm 0 (Nat.zero_le m)
  have hFrameAt := contDiffAt_smoothMetricFrame (hg.posDef hK hy) i
  have h := norm_iteratedFDeriv_comp_at_le g (fun A => smoothMetricFrame A i) y j hG hFrameAt C R
    (fun k hk => hFrame (g y) h0 (hg.2 y hy).1 (fun u => ((hg.2 y hy).2 u).1) i k (hk.trans hj))
    (fun k hk hkj => (hNorm k (hkj.trans hj)).trans (le_self_pow₀ hR (by omega)))
  exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity))
    (pow_le_pow_right₀ hR hj) (by positivity) (by positivity))

end CalderonN
