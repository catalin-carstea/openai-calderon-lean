module

public import Proof.CalderonN.FixedTube.CoarseReferenceRooms
public import Proof.CalderonN.GreenCross

import Proof.CalderonN.CompactProductCross
import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

theorem planeAnnulusObservation_subset_output : (planeAnnulusObservation normal) ⊆ (planeAnnulusOutput (dim := dim)) := by
  intro x hx
  have h9 : ‖x-(-(axis normal))‖ < (1/8 : ℝ) := by
    simpa only [dist_eq_norm] using mem_ball.mp hx
  have hn : ‖-(axis normal)‖ = 1 := by simp [axis]
  have hAdd := norm_add_le (x-(-(axis normal))) (-(axis normal))
  rw [sub_add_cancel,hn] at hAdd
  have hSub := norm_sub_le x (x-(-(axis normal)))
  rw [sub_sub_cancel,hn] at hSub
  change 4/5 < ‖x-0‖ ∧ ‖x-0‖ < 6/5
  rw [sub_zero]
  constructor <;> linarith

theorem planeAnnulus_isCompact_closure : IsCompact (closure (planeAnnulus (dim := dim))) :=
  (isCompact_closedBall (0 : (X dim)) 2).of_isClosed_subset isClosed_closure
    (closure_minimal (fun x hx => by
      rw [mem_closedBall,dist_eq_norm]
      exact (show ‖x-(0 : (X dim))‖ < 2 from hx.2).le)
      isClosed_closedBall)

theorem planeBall_isCompact_closure (r : ℝ) : IsCompact (closure (planeBall normal r)) :=
  (isCompact_closedBall (planeCenter normal) r).of_isClosed_subset isClosed_closure
    (closure_minimal ball_subset_closedBall isClosed_closedBall)

theorem planeAnnulusObservation_isCompact_closure : IsCompact (closure (planeAnnulusObservation normal)) :=
  (isCompact_closedBall (-(axis normal)) (1/8)).of_isClosed_subset isClosed_closure
    (closure_minimal ball_subset_closedBall isClosed_closedBall)

theorem closure_planeBall_obs_subset {δ : ℝ} (hδ : 0 < δ) :
    closure (planeBall normal (planeDepth-δ)) ⊆ planeBall normal (3*planeDepth) :=
  (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
    (closedBall_subset_ball (by
      have hd : 0 < planeDepth := by norm_num [planeDepth]
      linarith))

set_option maxHeartbeats 650000 in
/-- A local reference cross extends across the limiting plane. Its two
agreements continue throughout every lower-side slice present in the
source domain, using the connected output ball and annulus. -/
theorem exists_referencePlane_productSolution
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {δ C₁ C₂ γ₁ γ₂ : ℝ} (hδ : 0 < δ) (hδcap : δ ≤ planeDepth/100)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1)
    (hγ : 0 < γ₁+γ₂-1)
    (hO₁D₁ : planeBall normal (planeDepth+δ) ⊆ planeBall normal (3*planeDepth))
    (hI₁ : HarmonicInterpolation (isOpen_ball : IsOpen (planeBall normal (3*planeDepth)))
      (smoothMetric_restrict hg₁ (subset_univ _))
      (subset_closure.trans ((closure_planeBall_obs_subset (normal := normal)) hδ)) hO₁D₁ C₁ γ₁)
    (hI₂ : HarmonicInterpolation (isOpen_openAnnulus 0 (1/2) 2)
      (smoothMetric_restrict hg₂ (subset_univ _))
      (subset_closure.trans (closure_planeAnnulusObservation_subset (normal := normal)))
      (planeAnnulusOutput_subset (dim := dim)) C₂ γ₂)
    {L : Set (X dim)}
    {V : Set ((X dim) × (X dim))} {F : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ V F)
    (hBuffer₁ : closure (planeBall normal (3*planeDepth)) ×ˢ closure (planeAnnulusObservation normal) ⊆ V)
    (hBuffer₂ : closure (planeBall normal (planeDepth-δ)) ×ˢ closure (planeAnnulus (dim := dim)) ⊆ V)
    (hKnown₁ : planeBall normal (planeDepth+δ) ×ˢ ((planeAnnulusOutput (dim := dim)) ∩ L) ⊆ V)
    (hKnown₂ : (planeBall normal (planeDepth+δ) ∩ L) ×ˢ (planeAnnulusOutput (dim := dim)) ⊆ V) :
    ∃ G, ProductSolutionOn g₁ g₂ (planeBall normal (planeDepth+δ) ×ˢ (planeAnnulusOutput (dim := dim))) G ∧
      EqOn G F (planeBall normal (planeDepth+δ) ×ˢ ((planeAnnulusOutput (dim := dim)) ∩ L)) ∧
      EqOn G F ((planeBall normal (planeDepth+δ) ∩ L) ×ˢ (planeAnnulusOutput (dim := dim))) := by
  let D₁ := planeBall normal (3*planeDepth)
  let D₂ := (planeAnnulus (dim := dim))
  let S₁ := planeBall normal (planeDepth-δ)
  let S₂ := (planeAnnulusObservation normal)
  let O₁ := planeBall normal (planeDepth+δ)
  let O₂ := (planeAnnulusOutput (dim := dim))
  have hDepth : 0 < planeDepth := by norm_num [planeDepth]
  have hObsRadius : 0 < planeDepth-δ := by linarith
  have hOutputRadius : 0 < planeDepth+δ := by positivity
  have hS₁O₁ : S₁ ⊆ O₁ := ball_subset_ball (by linarith)
  have hS₂O₂ : S₂ ⊆ O₂ := (planeAnnulusObservation_subset_output (normal := normal))
  have hD₁ : IsOpen D₁ := isOpen_ball
  have hD₂ : IsOpen D₂ := isOpen_openAnnulus 0 (1/2) 2
  have hS₁ : IsOpen S₁ := isOpen_ball
  have hS₂ : IsOpen S₂ := isOpen_ball
  have hO₁ : IsOpen O₁ := isOpen_ball
  have hO₂ : IsOpen O₂ := isOpen_openAnnulus 0 (4/5) (6/5)
  have hS₁ne : S₁.Nonempty := nonempty_ball.mpr hObsRadius
  have hS₂ne : S₂.Nonempty := nonempty_ball.mpr (by norm_num)
  have hconn₁ : IsConnected D₁ := isConnected_ball (by positivity)
  have hconn₂ : IsConnected D₂ := isConnected_openAnnulus 0 (1/2) 2 (by norm_num) (by norm_num)
  have hOc₁ : IsConnected O₁ := isConnected_ball hOutputRadius
  have hOc₂ : IsConnected O₂ := isConnected_openAnnulus 0 (4/5) (6/5) (by norm_num) (by norm_num)
  have hMem₁ := product_memLp_of_compact_buffer hD₁ hS₂
    (((planeBall_isCompact_closure (normal := normal)) _).prod (planeAnnulusObservation_isCompact_closure (normal := normal)))
    (Set.prod_mono subset_closure subset_closure) (hF.1.continuousOn.mono hBuffer₁)
  have hMem₂ := product_memLp_of_compact_buffer hS₁ hD₂
    (((planeBall_isCompact_closure (normal := normal)) _).prod (planeAnnulus_isCompact_closure (dim := dim)))
    (Set.prod_mono subset_closure subset_closure) (hF.1.continuousOn.mono hBuffer₂)
  have hSD₁ : closure S₁ ⊆ D₁ := (closure_planeBall_obs_subset (normal := normal)) hδ
  have hSD₂ : S₂ ⊆ D₂ := subset_closure.trans (closure_planeAnnulusObservation_subset (normal := normal))
  have hgD₁ := smoothMetric_restrict hg₁ (subset_univ D₁)
  have hgD₂ := smoothMetric_restrict hg₂ (subset_univ D₂)
  have hfinite : (volume : Measure (X dim)) D₂ ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt (planeAnnulus_isCompact_closure (dim := dim)).measure_lt_top).ne
  obtain ⟨G,hG,hLeft,hRight⟩ := exists_productSolutionOn_cross_of_interpolation
    hD₁ hD₂ hconn₁ hconn₂ hS₁ hS₂ hS₁ne hS₂ne hO₁ hO₂ hO₁D₁ (planeAnnulusOutput_subset (dim := dim))
    ((planeBall_isCompact_closure (normal := normal)) _) hSD₁ hSD₂ hgD₁ hgD₂ hfinite hC₁ hC₂ hγ₂ hγ₂' hγ hI₁ hI₂
    hMem₁ hMem₂ (hF.mono ((Set.prod_mono subset_closure subset_closure).trans hBuffer₁))
    (hF.mono ((Set.prod_mono subset_closure subset_closure).trans hBuffer₂))
  refine ⟨G,hG,?_,?_⟩
  · intro q hq
    exact harmonic_eqOn_of_eqOn_open hO₁ hOc₁ hS₁ hS₁ne hS₁O₁
      (smoothMetric_restrict hg₁ (subset_univ O₁))
      (hG.harmonic_left hq.2.1) ((hF.mono hKnown₁).harmonic_left hq.2)
      (fun x hx => hRight (show (x,q.2) ∈ (O₁ ∩ S₁) ×ˢ O₂ from ⟨⟨hS₁O₁ hx,hx⟩,hq.2.1⟩)) hq.1
  · intro q hq
    exact harmonic_eqOn_of_eqOn_open hO₂ hOc₂ hS₂ hS₂ne hS₂O₂
      (smoothMetric_restrict hg₂ (subset_univ O₂))
      (hG.harmonic_right hq.1.1) ((hF.mono hKnown₂).harmonic_right hq.1)
      (fun y hy => hLeft (show (q.1,y) ∈ O₁ ×ˢ (O₂ ∩ S₂) from ⟨hq.1.1,⟨hS₂O₂ hy,hy⟩⟩)) hq.2

end CalderonN.FixedTube
