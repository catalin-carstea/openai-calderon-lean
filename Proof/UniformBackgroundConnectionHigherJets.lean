import Proof.UniversalMetricSprayJets
import Proof.BackgroundMetricSprayInputJets
import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def universalMetricConnectionSet (A D delta : ℝ) : Set MetricConnectionInput :=
  {q | ‖q.1‖ ≤ A ∧ ‖q.2‖ ≤ D ∧ delta ≤ |q.1.det|}

lemma isCompact_universalMetricConnectionSet (A D delta : ℝ) :
    IsCompact (universalMetricConnectionSet A D delta) := by
  have hClosed : IsClosed {q : MetricConnectionInput | delta ≤ |q.1.det|} :=
    isClosed_le continuous_const continuous_fst.matrix_det.abs
  have he : universalMetricConnectionSet A D delta =
      (Metric.closedBall (0:Mat) A ×ˢ Metric.closedBall (0:X →L[ℝ] Mat) D) ∩
        {q : MetricConnectionInput | delta ≤ |q.1.det|} := by
    ext q
    simp only [universalMetricConnectionSet,mem_ofPred_eq,mem_inter_iff,mem_prod,
      Metric.mem_closedBall,dist_zero_right]
    tauto
  rw [he]
  exact ((isCompact_closedBall (0:Mat) A).prod (isCompact_closedBall (0:X →L[ℝ] Mat) D)).inter_right hClosed

theorem exists_universalMetricConnection_jet_bound (A D delta : ℝ) (hDelta : 0 < delta) (N : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ n : ℕ,n ≤ N → ∀ q ∈ universalMetricConnectionSet A D delta,
      ‖iteratedFDeriv ℝ n universalMetricConnection q‖ ≤ C := by
  apply exists_finite_jet_bound_on_compact universalMetricConnection
    (universalMetricConnectionSet A D delta) (isCompact_universalMetricConnectionSet A D delta) _ N
  intro q hq
  apply contDiffAt_universalMetricConnection
  intro he
  have hh := hq.2.2
  rw [he,abs_zero] at hh
  exact (not_le_of_gt hDelta) hh

/-- All finite connection jets follow from finitely many frozen metric jets.
    Compactness is used only for a universal finite-dimensional rational map. -/
theorem uniform_background_connection_higher_jet_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N+1 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 0 < K) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),Background Ω K M g g₁ g₂ e →
      ∀ y ∈ Ω,∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (connectionBilinear g) y‖ ≤ C := by
  let B := backgroundAllMetricJetBudget M
  let delta := ((metricDensityBudget K)⁻¹)^2
  have hB : 0 ≤ B := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
  have hDelta : 0 < delta := by dsimp only [delta,metricDensityBudget];positivity
  obtain ⟨Cu,hCu,hUniversal⟩ := exists_universalMetricConnection_jet_bound K B delta hDelta N
  have hCu0 : 0 ≤ Cu := zero_le_one.trans hCu
  let C := 1+(N.factorial:ℝ)*Cu*(1+B)^N
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*Cu*(1+B)^N := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e h y hy n hn
  let F : X → MetricConnectionInput := fun x => (g x,fderiv ℝ g x)
  have hg (x : X) (hx : x ∈ Ω) : ContDiffAt ℝ ∞ g x :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (h.1.1 i j).contDiffAt (hΩ.mem_nhds hx)))
  have hF : ContDiffAt ℝ ∞ F y := (hg y hy).prodMk ((hg y hy).fderiv_right (m:=∞) (by simp))
  have hFG (j : ℕ) (hj : j ≤ N+1) : ‖iteratedFDeriv ℝ j g y‖ ≤ B :=
    (h.reference_matrix_jet_bound hΩ ⟨j,by omega⟩ hy).trans (abs_metricJet_le_all_budget M _)
  have hFJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j F y‖ ≤ B := by
    rw [iteratedFDeriv_prodMk (hg y hy) ((hg y hy).fderiv_right (m:=∞) (by simp)) (i:=j) (by simp),
      ContinuousMultilinearMap.opNorm_prod,norm_iteratedFDeriv_fderiv]
    exact max_le (hFG j (by omega)) (hFG (j+1) (by omega))
  have hMem : F y ∈ universalMetricConnectionSet K B delta := by
    refine ⟨?_,?_,h.1.det_lower_bound_of_density hK hy⟩
    · exact (Matrix.norm_le_iff hK.le).mpr (fun i j => h.1.entry_abs_bound hK hy i j)
    · simpa only [norm_iteratedFDeriv_one] using hFG 1 (by omega)
  have hU : ContDiffAt ℝ ∞ universalMetricConnection (F y) :=
    contDiffAt_universalMetricConnection _ (h.1.posDef hK hy).det_pos.ne'
  have he : universalMetricConnection ∘ F =ᶠ[𝓝 y] connectionBilinear g := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact universalMetricConnection_actual g x (hg x hx)
  rw [← (he.iteratedFDeriv ℝ n).eq_of_nhds]
  have hh := iteratedFDeriv_comp_common_bound F universalMetricConnection y hF hU N Cu (1+B) hCu0
    (by linarith only [hB]) (fun j hj => hUniversal j hj _ hMem)
    (fun j _ hj => (hFJets j hj).trans (by linarith)) n hn
  exact hh.trans (by dsimp only [C];linarith)

end ShrinkingSpheres
