module

public import Proof.CalderonN.UniformBackgroundSprayJets
public import Proof.CalderonN.LocalSmoothJetBudget

import Proof.CalderonN.CompactLocalJetBounds
import Proof.CalderonN.MatrixFieldJetNorms
import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! Finite Christoffel bounds from the frozen metric budgets. This uses
the same universal metric-jet locus as the checked spray estimates. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private def metricConnectionEntry (k i j : I dim) (p : MetricConnectionInput dim) : ℝ :=
  universalMetricConnection p (axis i) (axis j) k

private theorem metricConnectionEntry_actual_at (g : MetricField dim) (x : X dim)
    (hg : ContDiffAt ℝ ∞ g x) (k i j : I dim) :
    metricConnectionEntry k i j (g x,fderiv ℝ g x) = christoffel g x k i j := by
  rw [metricConnectionEntry,universalMetricConnection_actual g x hg,connectionBilinear_apply,
    connection_axis_components]

theorem uniform_background_christoffel_jet_budget {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N+1 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField dim) (e : Frame dim),Background Ω K M g g₁ g₂ e →
      ∀ x ∈ Ω,∀ k i j : I dim,LocalSmoothJetBudget (fun y => christoffel g y k i j) x N C := by
  let B := backgroundAllMetricJetBudget M
  have hB := backgroundAllMetricJetBudget_ge_one M
  let J := ellipticMatrixLocus dim K B ×ˢ closedBall (0 : X dim →L[ℝ] Mat dim) B
  have hJ : IsCompact J := (isCompact_ellipticMatrixLocus dim K B).prod (isCompact_closedBall _ _)
  have hSmooth (k i j : I dim) (q : MetricConnectionInput dim) (hq : q ∈ J) :
      ContDiffAt ℝ ∞ (metricConnectionEntry k i j) q :=
    (EuclideanSpace.proj (𝕜:=ℝ) k).contDiff.contDiffAt.comp q
      (((contDiffAt_universalMetricConnection q (ellipticMatrixLocus_posDef hK hq.1).det_pos.ne').clm_apply
        contDiffAt_const).clm_apply contDiffAt_const)
  choose G hG hCG using fun k i j => exists_uniform_local_finite_jet_bound hJ (hSmooth k i j) N
  let G₀ := 1+∑ k : I dim,∑ i : I dim,∑ j : I dim,G k i j
  have hG₀ : 1 ≤ G₀ := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => zero_le_one.trans (hG k i j))
  have hG₁ (k i j : I dim) : G k i j ≤ G₀ := by
    have hJ := Finset.single_le_sum (f := fun j : I dim => G k i j)
      (fun j _ => zero_le_one.trans (hG k i j)) (Finset.mem_univ j)
    have hI := Finset.single_le_sum (f := fun i : I dim => ∑ j : I dim,G k i j)
      (fun i _ => Finset.sum_nonneg fun j _ => zero_le_one.trans (hG k i j)) (Finset.mem_univ i)
    have hK' := Finset.single_le_sum (f := fun k : I dim => ∑ i : I dim,∑ j : I dim,G k i j)
      (fun k _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => zero_le_one.trans (hG k i j)) (Finset.mem_univ k)
    exact (hJ.trans (hI.trans hK')).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨(N.factorial:ℝ)*G₀*B^N,by
    have hN : (1:ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN hG₀) (one_le_pow₀ hB),?_⟩
  intro g g₁ g₂ e h x hx k i j
  let F (y : X dim) : MetricConnectionInput dim := (g y,fderiv ℝ g y)
  have hg (y : X dim) (hy : y ∈ Ω) : ContDiffAt ℝ ∞ g y :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr fun j => (h.1.1 i j).contDiffAt (hΩ.mem_nhds hy))
  have hGJ (j : ℕ) (hj : j ≤ N+1) : ‖iteratedFDeriv ℝ j g x‖ ≤ B := by
    have hM : ‖iteratedFDeriv ℝ j g x‖ ≤ |M ⟨j,by omega⟩| := by
      apply norm_iteratedFDeriv_matrix_le_of_entries g x j (hg x hx) (abs_nonneg _)
      intro a b
      exact (h.2.2.2.2.1 g (by simp) ⟨j,by omega⟩ a b x hx).trans (le_abs_self _)
    exact hM.trans (abs_metricJet_le_all_budget M _)
  have hF : LocalSmoothJetBudget F x N B := by
    refine ⟨(hg x hx).prodMk ((hg x hx).fderiv_right (m:=∞) (by simp)),?_⟩
    intro n hn
    rw [show F = fun y => (g y,fderiv ℝ g y) from rfl,
      iteratedFDeriv_prodMk (hg x hx) ((hg x hx).fderiv_right (m:=∞) (by simp)) (i:=n) (by simp),
      ContinuousMultilinearMap.opNorm_prod,norm_iteratedFDeriv_fderiv]
    exact max_le (hGJ n (by omega)) (hGJ (n+1) (by omega))
  have hMem : F x ∈ J := by
    have hG₀ := hGJ 0 (by omega)
    have hG₁ := hGJ 1 (by omega)
    rw [norm_iteratedFDeriv_zero] at hG₀
    rw [norm_iteratedFDeriv_one] at hG₁
    simp only [J,F,ellipticMatrixLocus,mem_prod,mem_inter_iff,mem_setOf_eq,mem_closedBall,dist_zero_right]
    exact ⟨⟨hG₀,(h.1.2 x hx).1,fun v => ((h.1.2 x hx).2 v).1⟩,hG₁⟩
  let Γ := metricConnectionEntry k i j
  have hΓ : LocalSmoothJetBudget Γ (F x) N G₀ :=
    ⟨hSmooth k i j _ hMem,fun n hn => (hCG k i j _ hMem n hn).trans (hG₁ k i j)⟩
  have hJ := hF.comp hΓ hB
  have hEq : Γ ∘ F =ᶠ[𝓝 x] fun y => christoffel g y k i j := by
    filter_upwards [hΩ.mem_nhds hx] with y hy using metricConnectionEntry_actual_at g y (hg y hy) k i j
  exact ⟨hJ.smooth.congr_of_eventuallyEq hEq.symm,fun n hn =>
    ((hEq.iteratedFDeriv ℝ n).eq_of_nhds).symm ▸ hJ.bound n hn⟩

end CalderonN
