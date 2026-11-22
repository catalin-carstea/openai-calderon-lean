module

public import Proof.CalderonN.FixedTube.CoarseReferenceCross
public import Proof.CalderonN.UniformProductCross

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

set_option maxHeartbeats 2300000

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- The same reference cross bounds the continued solution on the smaller
ball and annulus retained by the coarse covering. -/
theorem exists_uniform_bounded_planeReference
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (p₀ : P) {g₁ g₂ : P → (MetricField dim)}
    (hg₁ : ∀ p, SmoothMetric univ (g₁ p)) (hg₂ : ∀ p, SmoothMetric univ (g₂ p))
    (hb₁ : ∀ i j, ContDiff ℝ ∞ (fun q : P × (X dim) => divergenceCoeff (g₁ q.1) q.2 i j))
    (hb₂ : ∀ i j, ContDiff ℝ ∞ (fun q : P × (X dim) => divergenceCoeff (g₂ q.1) q.2 i j))
    {δ C₁ C₂ γ₁ γ₂ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ planeDepth/100)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1) (hγ : 0 < γ₁+γ₂-1)
    (hO₁D₁ : planeBall normal (planeDepth+δ) ⊆ planeBall normal (3*planeDepth))
    (hInterp : ∀ᶠ p in 𝓝 p₀,
      HarmonicInterpolation (isOpen_ball : IsOpen (planeBall normal (3*planeDepth)))
        (smoothMetric_restrict (hg₁ p) (subset_univ _))
        (subset_closure.trans ((closure_planeBall_obs_subset (normal := normal)) hδ)) hO₁D₁ C₁ γ₁ ∧
      HarmonicInterpolation (isOpen_openAnnulus 0 (1/2) 2)
        (smoothMetric_restrict (hg₂ p) (subset_univ _))
        (subset_closure.trans (closure_planeAnnulusObservation_subset (normal := normal)))
        (planeAnnulusOutput_subset (dim := dim)) C₂ γ₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ p in 𝓝 p₀,
      ∀ (F : (X dim) × (X dim) → ℝ) (M : ℝ), 0 ≤ M →
      ProductSolutionOn (g₁ p) (g₂ p) (planeBall normal (3*planeDepth) ×ˢ (planeAnnulusObservation normal)) F →
      ProductSolutionOn (g₁ p) (g₂ p) (planeBall normal (planeDepth-δ) ×ˢ (planeAnnulus (dim := dim))) F →
      (∀ q ∈ (planeBall normal (3*planeDepth) ×ˢ (planeAnnulusObservation normal)) ∪
          (planeBall normal (planeDepth-δ) ×ˢ (planeAnnulus (dim := dim))), |F q| ≤ M) →
      ∃ G, ProductSolutionOn (g₁ p) (g₂ p) (planeBall normal (planeDepth+δ) ×ˢ (planeAnnulusOutput (dim := dim))) G ∧
        EqOn G F (planeBall normal (planeDepth+δ) ×ˢ (planeAnnulusObservation normal)) ∧
        ∀ q ∈ closedBall (0 : (X dim)) (δ/2) ×ˢ closedAnnulus (0 : (X dim)) (9/10) (11/10), |G q| ≤ C*M := by
  obtain ⟨r,hr,hrI⟩ := Metric.mem_nhds_iff.mp hInterp
  let J := closedBall p₀ (r/2)
  have hI (p : P) (hp : p ∈ J) := hrI (closedBall_subset_ball (half_lt_self hr) hp)
  have hD : 0 < planeDepth := by norm_num [planeDepth]
  have hObs : 0 < planeDepth-δ := by linarith
  have hCball : closedBall (0 : (X dim)) (δ/2) ⊆ planeBall normal (planeDepth+δ) := by
    intro x hx
    have hn : ‖x‖ ≤ δ/2 := mem_closedBall_zero_iff.mp hx
    have hc : ‖(planeCenter normal)‖ = planeDepth := by simp [planeCenter,planeDepth,norm_smul,axis]
    rw [planeBall,mem_ball,dist_eq_norm]
    have h := norm_sub_le x (planeCenter normal)
    linarith
  have hCann : closedAnnulus (0 : (X dim)) (9/10) (11/10) ⊆ (planeAnnulusOutput (dim := dim)) := by
    intro x hx
    obtain ⟨hl,hu⟩ := mem_closedAnnulus.mp hx
    exact ⟨by linarith,by linarith⟩
  obtain ⟨C,hC,h⟩ := exists_uniform_bounded_productCross
    (J := J) (isCompact_closedBall _ _) isOpen_ball (isOpen_openAnnulus 0 (1/2) 2)
    (isConnected_ball (by positivity)) (isConnected_openAnnulus 0 (1/2) 2 (by norm_num) (by norm_num))
    isOpen_ball isOpen_ball (nonempty_ball.mpr hObs) (nonempty_ball.mpr (by norm_num))
    isOpen_ball (isOpen_openAnnulus 0 (4/5) (6/5))
    ((planeBall_isCompact_closure (normal := normal)) _) ((closure_planeBall_obs_subset (normal := normal)) hδ)
    (subset_closure.trans (closure_planeAnnulusObservation_subset (normal := normal))) hO₁D₁ (planeAnnulusOutput_subset (dim := dim))
    ((planeBall_isCompact_closure (normal := normal)) _) (planeAnnulus_isCompact_closure (dim := dim))
    (isCompact_closedBall _ _) (isCompact_closedAnnulus _ _ _) hCball hCann
    (fun p _ => smoothMetric_restrict (hg₁ p) (subset_univ _))
    (fun p _ => smoothMetric_restrict (hg₂ p) (subset_univ _))
    (fun i j => (hb₁ i j).contDiffOn) (fun i j => (hb₂ i j).contDiffOn)
    hC₁ hC₂ hγ₂ hγ₂' hγ (fun p hp => (hI p hp).1) (fun p hp => (hI p hp).2)
  refine ⟨C,hC,?_⟩
  filter_upwards [closedBall_mem_nhds p₀ (half_pos hr)] with p hp F M hM hFa hFb hB
  obtain ⟨G,hG,hLeft,_,hBnd⟩ := h p hp F M hM hFa hFb hB
  exact ⟨G,hG,hLeft.mono (prod_mono Subset.rfl (subset_inter (planeAnnulusObservation_subset_output (normal := normal)) Subset.rfl)),hBnd⟩

end CalderonN.FixedTube
