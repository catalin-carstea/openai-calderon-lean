import Proof.RadialTaylorHigherJets
import Proof.MatrixFieldHigherJetNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma norm_matrixEntryL_le_one (i j : I) : ‖matrixEntryL i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  simpa only [matrixEntryL_apply,one_mul] using Matrix.norm_entry_le_entrywise_sup_norm A (i:=i) (j:=j)

def frameAxisCoordinateL (j k : I) : (X →L[ℝ] X) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜:=ℝ) k).comp (ContinuousLinearMap.apply ℝ X (axis j))

lemma norm_frameAxisCoordinateL_le_one (j k : I) : ‖frameAxisCoordinateL j k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖(L (axis j)) k‖ ≤ 1*‖L‖
  exact (PiLp.norm_apply_le (L (axis j)) k).trans ((L.le_opNorm (axis j)).trans_eq (by rw [norm_axis];ring))

/-- The coframe contraction has uniform finite mixed jets linear in the
    fixed vector. Only the metric and independent normalized-frame jets occur. -/
theorem norm_iteratedFDeriv_matrix_coframe_le
    (A : P → Mat) (L : P → X →L[ℝ] X) (p : P)
    (hA : ContDiffAt ℝ ∞ A p) (hL : ContDiffAt ℝ ∞ L p)
    (N : ℕ) (CA CL : ℝ) (hCA : 0 ≤ CA) (hCL : 0 ≤ CL)
    (hAJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n A p‖ ≤ CA)
    (hLJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n L p‖ ≤ CL)
    (v : X) (j : I) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun q => ∑ i : I,∑ k : I,A q i k*v i*(L q (axis j)) k) p‖ ≤
      (9*2^N*CA*CL)*‖v‖ := by
  let f := fun i k q => A q i k
  let g := fun k q => (L q (axis j)) k
  have hf (i k : I) : ContDiffAt ℝ ∞ (f i k) p := (matrixEntryL i k).contDiff.contDiffAt.comp p hA
  have hg (k : I) : ContDiffAt ℝ ∞ (g k) p := (frameAxisCoordinateL j k).contDiff.contDiffAt.comp p hL
  have hfJ (i k : I) (m : ℕ) (hm : m ≤ N) : ‖iteratedFDeriv ℝ m (f i k) p‖ ≤ CA :=
    (norm_iteratedFDeriv_clm_comp_le (matrixEntryL i k) A p hA m).trans
      ((mul_le_mul (norm_matrixEntryL_le_one i k) (hAJets m hm) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hgJ (k : I) (m : ℕ) (hm : m ≤ N) : ‖iteratedFDeriv ℝ m (g k) p‖ ≤ CL :=
    (norm_iteratedFDeriv_clm_comp_le (frameAxisCoordinateL j k) L p hL m).trans
      ((mul_le_mul (norm_frameAxisCoordinateL_le_one j k) (hLJets m hm) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  let term := fun i k q => v i*(f i k q*g k q)
  have ht (i k : I) : ContDiffAt ℝ ∞ (term i k) p := contDiffAt_const.mul ((hf i k).mul (hg k))
  have hTerm (i k : I) : ‖iteratedFDeriv ℝ n (term i k) p‖ ≤ (2^N*CA*CL)*‖v‖ := by
    change ‖iteratedFDeriv ℝ n (fun q => v i • (f i k q*g k q)) p‖ ≤ _
    rw [norm_iteratedFDeriv_const_smul_at _ p ((hf i k).mul (hg k)) (v i) n]
    have hProd := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.lsmul ℝ ℝ)
      (f i k) (g k) p (hf i k) (hg k) N CA CL hCA hCL (hfJ i k) (hgJ k) n hn
    have hProd' : ‖iteratedFDeriv ℝ n (fun q => f i k q*g k q) p‖ ≤ 2^N*CA*CL :=
      hProd.trans (by
        calc
          _ = ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖*(2^N*CA*CL) := by ring
          _ ≤ 1*(2^N*CA*CL) := mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le (by positivity)
          _ = _ := one_mul _)
    have hv : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    exact (mul_le_mul hv hProd' (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring)
  have hEq : (fun q => ∑ i : I,∑ k : I,A q i k*v i*(L q (axis j)) k) =
      fun q => ∑ i : I,∑ k : I,term i k q := by
    funext q
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [term,f,g]
    ring
  rw [hEq]
  have hh := norm_iteratedFDeriv_fintype_sum_at_le (fun i : I => fun q => ∑ k : I,term i k q) p
    (fun i => ContDiffAt.sum (fun k _ => ht i k)) n
  exact hh.trans ((Finset.sum_le_sum (fun i _ =>
    (norm_iteratedFDeriv_fintype_sum_at_le (fun k : I => term i k) p (ht i) n).trans
      (Finset.sum_le_sum (fun k _ => hTerm i k)))).trans_eq (by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,I];ring))

end ShrinkingSpheres
