import Proof.MatrixFieldHigherJetNorms
import Proof.NormalFrameMatrixInputJets
import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

lemma Background.first_matrix_jet_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (j : Fin (m+1)) {y : X} (hy : y ∈ Ω) :
    ‖iteratedFDeriv ℝ j.val g₁ y‖ ≤ |M j| := by
  have hSmooth : ContDiffAt ℝ ∞ g₁ y :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun k => (h.2.1.1 i k).contDiffAt (hΩ.mem_nhds hy)))
  exact norm_iteratedFDeriv_matrix_le_of_entries g₁ y hSmooth j.val |M j| (abs_nonneg _)
    (fun i k => (h.2.2.2.2.1 g₁ (by simp) j i k y hy).trans (le_abs_self _))

lemma Elliptic.diagonal_entry_mem_Icc {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (i : I) :
    g y i i ∈ Icc K⁻¹ K := by
  have hLo := ((h.2 y hy).2 (axis i)).1
  have hEntry : metricPair g y (axis i) (axis i) = g y i i := by simp [metricPair,axis]
  rw [norm_axis,one_pow,mul_one,hEntry] at hLo
  exact ⟨hLo,(le_abs_self _).trans (h.entry_abs_bound hK hy i i)⟩

def normalFrameCentralEntries (g g₁ : MetricField) (q : NormalFrameParameter × X) : ℝ × ℝ :=
  (g q.1.1 0 0,g₁ q.1.1 0 0)

lemma Background.contDiffAt_normalFrameCentralEntries {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) {q : NormalFrameParameter × X} (hq : q.1.1 ∈ Ω) :
    ContDiffAt ℝ ∞ (normalFrameCentralEntries g g₁) q :=
  (((h.1.1 0 0).contDiffAt (hΩ.mem_nhds hq)).comp q contDiffAt_fst.fst).prodMk
    (((h.2.1.1 0 0).contDiffAt (hΩ.mem_nhds hq)).comp q contDiffAt_fst.fst)

theorem Background.normalFrameCentralEntries_jet_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (N : ℕ) (hNm : N ≤ m)
    {q : NormalFrameParameter × X} (hq : q.1.1 ∈ Ω) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (normalFrameCentralEntries g g₁) q‖ ≤
      (N.factorial:ℝ)*backgroundAllMetricJetBudget M := by
  let B := backgroundAllMetricJetBudget M
  let F : X → ℝ × ℝ := fun x => (g x 0 0,g₁ x 0 0)
  have hA := (h.1.1 0 0).contDiffAt (hΩ.mem_nhds hq)
  have hB := (h.2.1.1 0 0).contDiffAt (hΩ.mem_nhds hq)
  have hF : ContDiffAt ℝ ∞ F q.1.1 := hA.prodMk hB
  have hJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j F q.1.1‖ ≤ B := by
    rw [iteratedFDeriv_prodMk hA hB (i:=j) (by simp),ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact (h.reference_jet_bound ⟨j,by omega⟩ hq 0 0).trans ((le_abs_self _).trans (abs_metricJet_le_all_budget M _))
    · exact (h.2.2.2.2.1 g₁ (by simp) ⟨j,by omega⟩ 0 0 _ hq).trans
        ((le_abs_self _).trans (abs_metricJet_le_all_budget M _))
  let pi : (NormalFrameParameter × X) →L[ℝ] X :=
    (ContinuousLinearMap.fst ℝ X (ℝ × (X →L[ℝ] X))).comp (ContinuousLinearMap.fst ℝ NormalFrameParameter X)
  have hpi : ‖pi‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.1.1‖ ≤ 1*‖p‖
    simpa only [one_mul] using (norm_fst_le p.1).trans (norm_fst_le p)
  have hh := iteratedFDeriv_comp_common_bound pi F q pi.contDiff.contDiffAt hF N B 1
    (zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)) le_rfl hJets
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one pi hpi q j hj) n hn
  change ‖iteratedFDeriv ℝ n (normalFrameCentralEntries g g₁) q‖ ≤
    (N.factorial:ℝ)*backgroundAllMetricJetBudget M*1^N at hh
  simpa only [one_pow,mul_one] using hh

end ShrinkingSpheres
