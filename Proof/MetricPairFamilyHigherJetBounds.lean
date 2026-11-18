import Proof.MatrixCoframeHigherJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- Uniform finite jets of a moving metric contraction. One vector factor
    may carry the quadratic geometric gain and the other only a coarse budget. -/
theorem norm_iteratedFDeriv_metricPair_families_le
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P → Mat) (v w : P → X) (p : P)
    (hA : ContDiffAt ℝ ∞ A p) (hv : ContDiffAt ℝ ∞ v p) (hw : ContDiffAt ℝ ∞ w p)
    (N : ℕ) (CA Cv Cw : ℝ) (hCA : 0 ≤ CA) (hCv : 0 ≤ Cv) (hCw : 0 ≤ Cw)
    (hAJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n A p‖ ≤ CA)
    (hvJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n v p‖ ≤ Cv)
    (hwJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n w p‖ ≤ Cw)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun q => ∑ i : I,∑ j : I,A q i j*v q i*w q j) p‖ ≤
      9*(2^N*(2^N*CA*Cv)*Cw) := by
  let f := fun i j q => A q i j
  let vi := fun i q => (v q) i
  let wi := fun j q => (w q) j
  have hf (i j : I) : ContDiffAt ℝ ∞ (f i j) p := (matrixEntryL i j).contDiff.contDiffAt.comp p hA
  have hvi (i : I) : ContDiffAt ℝ ∞ (vi i) p := (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffAt.comp p hv
  have hwi (j : I) : ContDiffAt ℝ ∞ (wi j) p := (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.contDiffAt.comp p hw
  have hProj (i : I) : ‖(EuclideanSpace.proj (𝕜:=ℝ) i : X →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x i‖ ≤ 1*‖x‖
    simpa only [one_mul] using PiLp.norm_apply_le x i
  have hfJ (i j : I) (k : ℕ) (hk : k ≤ N) : ‖iteratedFDeriv ℝ k (f i j) p‖ ≤ CA :=
    (norm_iteratedFDeriv_clm_comp_le (matrixEntryL i j) A p hA k).trans
      ((mul_le_mul (norm_matrixEntryL_le_one i j) (hAJets k hk) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hvJ (i : I) (k : ℕ) (hk : k ≤ N) : ‖iteratedFDeriv ℝ k (vi i) p‖ ≤ Cv :=
    (norm_iteratedFDeriv_clm_comp_le (EuclideanSpace.proj (𝕜:=ℝ) i) v p hv k).trans
      ((mul_le_mul (hProj i) (hvJets k hk) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hwJ (j : I) (k : ℕ) (hk : k ≤ N) : ‖iteratedFDeriv ℝ k (wi j) p‖ ≤ Cw :=
    (norm_iteratedFDeriv_clm_comp_le (EuclideanSpace.proj (𝕜:=ℝ) j) w p hw k).trans
      ((mul_le_mul (hProj j) (hwJets k hk) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hMulNorm : ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  have hfvJ (i j : I) (k : ℕ) (hk : k ≤ N) :
      ‖iteratedFDeriv ℝ k (fun q => f i j q*vi i q) p‖ ≤ 2^N*CA*Cv := by
    have hh := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.lsmul ℝ ℝ)
      (f i j) (vi i) p (hf i j) (hvi i) N CA Cv hCA hCv (hfJ i j) (hvJ i) k hk
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hMulNorm (show 0 ≤ 2^N*CA*Cv by positivity)])
  let term := fun i j q => f i j q*vi i q*wi j q
  have ht (i j : I) : ContDiffAt ℝ ∞ (term i j) p := ((hf i j).mul (hvi i)).mul (hwi j)
  have htJ (i j : I) : ‖iteratedFDeriv ℝ n (term i j) p‖ ≤ 2^N*(2^N*CA*Cv)*Cw := by
    have hh := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.lsmul ℝ ℝ)
      (fun q => f i j q*vi i q) (wi j) p ((hf i j).mul (hvi i)) (hwi j)
      N (2^N*CA*Cv) Cw (by positivity) hCw (hfvJ i j) (hwJ j) n hn
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hMulNorm (show 0 ≤ 2^N*(2^N*CA*Cv)*Cw by positivity)])
  change ‖iteratedFDeriv ℝ n (fun q => ∑ i : I,∑ j : I,term i j q) p‖ ≤ _
  have hh := norm_iteratedFDeriv_fintype_sum_at_le (fun i : I => fun q => ∑ j : I,term i j q) p
    (fun i => ContDiffAt.sum (fun j _ => ht i j)) n
  exact hh.trans ((Finset.sum_le_sum (fun i _ =>
    (norm_iteratedFDeriv_fintype_sum_at_le (fun j : I => term i j) p (ht i) n).trans
      (Finset.sum_le_sum (fun j _ => htJ i j)))).trans_eq
      (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,I];ring))

end ShrinkingSpheres
