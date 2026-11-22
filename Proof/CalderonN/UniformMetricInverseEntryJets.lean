module

public import Proof.CalderonN.UniformBackgroundChristoffelJets

import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.CompactLocalJetBounds
import Mathlib.Tactic

/-! Uniform jets of an inverse metric entry on the compact elliptic
locus used by the coordinate trace coefficients. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem uniform_metric_inverse_entry_jet_budget
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : MetricField dim),Elliptic Ω K g →
      (∀ (k : Fin (m+1)) i j,∀ y ∈ Ω,‖iteratedFDeriv ℝ k.val (fun x => g x i j) y‖ ≤ M k) →
      ∀ x ∈ Ω,∀ i j : I dim,LocalSmoothJetBudget (fun y => (g y)⁻¹ i j) x N C := by
  let D := backgroundAllMetricJetBudget M
  have hD := backgroundAllMetricJetBudget_ge_one M
  let J := ellipticMatrixLocus dim K D
  have hJ : IsCompact J := isCompact_ellipticMatrixLocus dim K D
  let U := {A : Mat dim | A.det ≠ 0}
  have hEntry (i j : I dim) : ContDiff ℝ ∞ (fun A : Mat dim => A i j) := (matrixEntryL i j).contDiff
  have hU : IsOpen U :=
    isOpen_ne.preimage (contDiffOn_univ.mp (contDiffOn_det_of_entries
      (fun i j => (hEntry i j).contDiffOn))).continuous
  have hInv (i j : I dim) (A : Mat dim) (hA : A ∈ J) :
      ContDiffAt ℝ ∞ (fun A : Mat dim => A⁻¹ i j) A :=
    (contDiffOn_inv_entry_of_entries (fun i j => (hEntry i j).contDiffOn)
      (show ∀ A ∈ U,A.det ≠ 0 from fun _ h => h) i j).contDiffAt
        (hU.mem_nhds ((ellipticMatrixLocus_posDef hK hA).det_pos.ne'))
  choose B hB hInvB using fun i j => exists_uniform_local_finite_jet_bound hJ (hInv i j) N
  let B₀ := 1+∑ i : I dim,∑ j : I dim,B i j
  have hB₀ : 1 ≤ B₀ := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => zero_le_one.trans (hB i j))
  have hBound (i j : I dim) : B i j ≤ B₀ :=
    ((Finset.single_le_sum (fun k _ => zero_le_one.trans (hB i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => zero_le_one.trans (hB k l))
        (Finset.mem_univ i))).trans (le_add_of_nonneg_left zero_le_one)
  have hn : (1:ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
  refine ⟨(N.factorial:ℝ)*B₀*D^N,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hn hB₀) (one_le_pow₀ hD),?_⟩
  intro g hg hJets x hx i j
  have hSmooth : ContDiffAt ℝ ∞ g x := contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
    (hg.1 i j).contDiffAt (hΩ.mem_nhds hx)
  have hgJ : LocalSmoothJetBudget g x N D := by
    refine ⟨hSmooth,fun k hk => ?_⟩
    have hE : ‖iteratedFDeriv ℝ k g x‖ ≤ |M ⟨k,by omega⟩| := by
      apply norm_iteratedFDeriv_matrix_le_of_entries g x k hSmooth (abs_nonneg _)
      exact fun a b => (hJets ⟨k,by omega⟩ a b x hx).trans (le_abs_self _)
    exact hE.trans (abs_metricJet_le_all_budget M _)
  have hMem : g x ∈ J :=
    ⟨mem_closedBall_zero_iff.mpr hgJ.value_norm_le,(hg.2 x hx).1,fun v => ((hg.2 x hx).2 v).1⟩
  have hI : LocalSmoothJetBudget (fun A : Mat dim => A⁻¹ i j) (g x) N B₀ :=
    ⟨hInv i j (g x) hMem,fun k hk => (hInvB i j (g x) hMem k hk).trans (hBound i j)⟩
  exact hgJ.comp hI hD

end CalderonN
