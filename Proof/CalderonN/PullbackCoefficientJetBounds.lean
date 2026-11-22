module

public import Proof.CalderonN.FirstMetricNormalJets
public import Proof.CalderonN.MatrixFieldJetNorms

import Proof.CalderonN.SecondDerivativeCompositionBounds
import Proof.CalderonN.MetricCalculus
public import Proof.CalderonN.LinearMetric
import Proof.CalderonN.MetricConnection
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-! Uniform bounds for the smooth coefficient map used in the actual
normal pullback, on elliptic matrix and frame data. -/

public section

noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev PullbackCoefficientData (dim : ℕ) := Mat dim × (X dim →L[ℝ] X dim)

@[expose] def pullbackMetricMatrix (q : PullbackCoefficientData dim) : Mat dim :=
  (coordinateMatrix q.2)ᵀ * q.1 * coordinateMatrix q.2

@[expose] def pullbackDivergenceMatrix (q : PullbackCoefficientData dim) : Mat dim :=
  Real.sqrt (pullbackMetricMatrix q).det • (pullbackMetricMatrix q)⁻¹

theorem contDiff_pullbackMetricMatrix : ContDiff ℝ ∞ (pullbackMetricMatrix (dim := dim)) := by
  have hL (i j : I dim) : ContDiff ℝ ∞ (fun q : PullbackCoefficientData dim => coordinateMatrix q.2 i j) := by
    simp only [coordinateMatrix_apply]
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
      (contDiff_snd.clm_apply (contDiff_const (c := axis j)))
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [pullbackMetricMatrix,Matrix.mul_apply,Matrix.transpose_apply]
  have hA (a b : I dim) : ContDiff ℝ ∞ (fun q : PullbackCoefficientData dim => q.1 a b) :=
    contDiff_pi.mp (contDiff_pi.mp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : PullbackCoefficientData dim → Mat dim)) a) b
  exact ContDiff.sum fun a _ =>
    (ContDiff.sum fun b _ => (hL b i).mul (hA b a)).mul (hL a j)

theorem pullbackMetricMatrix_posDef {q : PullbackCoefficientData dim}
    (hA : q.1.PosDef) (hT : Function.Injective q.2) : (pullbackMetricMatrix q).PosDef := by
  have hM : Function.Injective ((coordinateMatrix q.2).mulVec) := by
    intro u v h
    let U : X dim := WithLp.toLp 2 u
    let V : X dim := WithLp.toLp 2 v
    have he : q.2 U = q.2 V := by
      ext i
      have he := congrFun h i
      simpa only [U,V,← coordinateMatrix_mulVec q.2] using he
    exact congrArg WithLp.ofLp (hT he)
  have hEq : (coordinateMatrix q.2)ᴴ = (coordinateMatrix q.2)ᵀ := by
    ext i j
    exact star_trivial _
  rw [pullbackMetricMatrix,← hEq]
  exact hA.conjTranspose_mul_mul_same hM

private theorem contDiffOn_pullbackDivergenceMatrix :
    ContDiffOn ℝ ∞ (pullbackDivergenceMatrix (dim := dim))
      {q | 0 < (pullbackMetricMatrix q).det} := by
  let U := {q : PullbackCoefficientData dim | 0 < (pullbackMetricMatrix q).det}
  have hM (i j : I dim) : ContDiffOn ℝ ∞ (fun q => pullbackMetricMatrix q i j) U :=
    (contDiff_pi.mp (contDiff_pi.mp (contDiff_pullbackMetricMatrix (dim := dim)) i) j).contDiffOn
  have hDet : ContDiffOn ℝ ∞ (fun q => (pullbackMetricMatrix q).det) U :=
    contDiffOn_det_of_entries hM
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  change ContDiffOn ℝ ∞ (fun q => Real.sqrt (pullbackMetricMatrix q).det * (pullbackMetricMatrix q)⁻¹ i j) U
  exact (hDet.sqrt (fun q hq => (show 0 < (pullbackMetricMatrix q).det from hq).ne')).mul
    (contDiffOn_inv_entry_of_entries hM (fun q hq => (show 0 < (pullbackMetricMatrix q).det from hq).ne') i j)

theorem contDiffAt_pullbackDivergenceMatrix_of_posDef (q : PullbackCoefficientData dim)
    (h : (pullbackMetricMatrix q).PosDef) :
    ContDiffAt ℝ ∞ pullbackDivergenceMatrix q := by
  let U := {p : PullbackCoefficientData dim | 0 < (pullbackMetricMatrix p).det}
  have hU : IsOpen U := isOpen_lt continuous_const
    (contDiffOn_univ.mp (contDiffOn_det_of_entries (fun i j =>
      ((contDiff_pi.mp (contDiff_pi.mp (contDiff_pullbackMetricMatrix (dim := dim)) i)) j).contDiffOn))).continuous
  exact contDiffOn_pullbackDivergenceMatrix.contDiffAt (hU.mem_nhds h.det_pos)

/-- The pointwise coefficient map has common bounds for three jets over a
closed family of uniformly elliptic matrices and uniformly invertible frames. -/
theorem exists_pullbackDivergenceMatrix_third_jet_bound (dim : ℕ) [NeZero dim] (K L : ℝ) (hK : 0 < K) :
    ∃ B ≥ (0 : ℝ), ∀ q : PullbackCoefficientData dim,
      ‖q‖ ≤ L → q.1.transpose = q.1 →
      (∀ u, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => q.1) 0 u u) →
      (∀ u, ‖u‖ ≤ 2*K*‖q.2 u‖) →
      ContDiffAt ℝ ∞ pullbackDivergenceMatrix q ∧
      ‖fderiv ℝ pullbackDivergenceMatrix q‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ pullbackDivergenceMatrix) q‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ pullbackDivergenceMatrix)) q‖ ≤ B ∧
      ‖pullbackDivergenceMatrix q‖ ≤ B := by
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
  let U := {q : P | 0 < (pullbackMetricMatrix q).det}
  have hU : IsOpen U := isOpen_lt continuous_const
    (contDiffOn_univ.mp (contDiffOn_det_of_entries (fun i j =>
      ((contDiff_pi.mp (contDiff_pi.mp (contDiff_pullbackMetricMatrix (dim := dim)) i)) j).contDiffOn))).continuous
  have hJU : J ⊆ U := by
    intro q hq
    have hCq : q ∈ C := hq.2
    have hA : q.1.PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hCq.1) ?_
      intro u hu
      let w : X dim := WithLp.toLp 2 u
      have hw : w ≠ 0 := fun h => hu (congrArg WithLp.ofLp h)
      have hp := (mul_pos (inv_pos.mpr hK) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hw))).trans_le (hCq.2.1 w)
      simpa only [metricPair,w,Matrix.mulVec,dotProduct,Finset.mul_sum,star_trivial,mul_assoc,mul_left_comm] using hp
    have hT : Function.Injective q.2 := by
      intro a b h
      have hN := hCq.2.2 (a-b)
      rw [map_sub,h,sub_self,norm_zero,mul_zero] at hN
      exact sub_eq_zero.mp (norm_le_zero_iff.mp hN)
    exact (pullbackMetricMatrix_posDef hA hT).det_pos
  have hf : ContDiffOn ℝ ∞ pullbackDivergenceMatrix U := contDiffOn_pullbackDivergenceMatrix
  have hD := hf.fderiv_of_isOpen (m := ∞) hU (by simp)
  have hDD := hD.fderiv_of_isOpen (m := ∞) hU (by simp)
  have hDDD := hDD.fderiv_of_isOpen (m := ∞) hU (by simp)
  have hNorm := (((hD.continuousOn.norm.add hDD.continuousOn.norm).add hDDD.continuousOn.norm).add
    hf.continuousOn.norm).mono hJU
  obtain ⟨B,hB⟩ := hJ.exists_bound_of_continuousOn hNorm
  refine ⟨max 0 B,le_max_left _ _,fun q hq hSym hLow hInv => ?_⟩
  have hqJ : q ∈ J := ⟨by simpa only [mem_closedBall,dist_zero_right] using hq,⟨hSym,hLow,hInv⟩⟩
  have hqB : ‖fderiv ℝ pullbackDivergenceMatrix q‖ +
      ‖fderiv ℝ (fderiv ℝ pullbackDivergenceMatrix) q‖ +
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ pullbackDivergenceMatrix)) q‖ +
      ‖pullbackDivergenceMatrix q‖ ≤ max 0 B :=
    (le_abs_self _).trans ((hB q hqJ).trans (le_max_right _ _))
  have h3 := (le_add_of_nonneg_right (norm_nonneg _)).trans hqB
  have h2 := (le_add_of_nonneg_right (norm_nonneg _)).trans h3
  exact ⟨hf.contDiffAt (hU.mem_nhds (hJU hqJ)),
    (le_add_of_nonneg_right (norm_nonneg _)).trans h2,
    (le_add_of_nonneg_left (norm_nonneg _)).trans h2,
    (le_add_of_nonneg_left (by positivity)).trans h3,
    (le_add_of_nonneg_left (by positivity)).trans hqB⟩

theorem exists_pullbackDivergenceMatrix_jet_bound (dim : ℕ) [NeZero dim] (K L : ℝ) (hK : 0 < K) :
    ∃ B ≥ (0 : ℝ), ∀ q : PullbackCoefficientData dim,
      ‖q‖ ≤ L → q.1.transpose = q.1 →
      (∀ u, K⁻¹*‖u‖^2 ≤ metricPair (fun _ => q.1) 0 u u) →
      (∀ u, ‖u‖ ≤ 2*K*‖q.2 u‖) →
      ContDiffAt ℝ ∞ pullbackDivergenceMatrix q ∧
      ‖fderiv ℝ pullbackDivergenceMatrix q‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ pullbackDivergenceMatrix) q‖ ≤ B := by
  obtain ⟨B,hB,h⟩ := exists_pullbackDivergenceMatrix_third_jet_bound dim K L hK
  refine ⟨B,hB,fun q hq hSym hLow hInv => ?_⟩
  obtain ⟨hs,h1,h2,_⟩ := h q hq hSym hLow hInv
  exact ⟨hs,h1,h2⟩

end CalderonN
