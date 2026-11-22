module

public import Proof.CalderonN.FixedTube.ConnectedInterpolation
public import Proof.CalderonN.FixedTube.RadialCollars

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- The large ball on the near-plane side is centered one depth below
the limiting plane. Its radius is three times that depth. -/
@[expose] def planeDepth : ℝ := 1/32

@[expose] def planeCenter (normal : I dim) : (X dim) := -(planeDepth • axis normal)

@[expose] def planeBall (normal : I dim) (r : ℝ) : Set (X dim) := ball (planeCenter normal) r

@[expose] def planeAnnulus : Set (X dim) := openAnnulus 0 (1/2) 2

@[expose] def planeAnnulusObservation (normal : I dim) : Set (X dim) := ball (-(axis normal)) (1/8)

@[expose] def planeAnnulusOutput : Set (X dim) := openAnnulus 0 (4/5) (6/5)

theorem closure_planeAnnulusObservation_subset :
    closure (planeAnnulusObservation normal) ⊆ (planeAnnulus (dim := dim)) := by
  refine (closure_minimal ball_subset_closedBall isClosed_closedBall).trans ?_
  intro x hx
  have hNorm : ‖x - (-(axis normal))‖ ≤ 1/8 := by
    simpa only [dist_eq_norm] using mem_closedBall.mp hx
  have hUnit : ‖-(axis normal)‖ = 1 := by simp [axis]
  have hAdd := norm_add_le (x-(-(axis normal))) (-(axis normal))
  rw [sub_add_cancel,hUnit] at hAdd
  have hSub := norm_sub_le x (x-(-(axis normal)))
  rw [sub_sub_cancel,hUnit] at hSub
  change 1/2 < ‖x-0‖ ∧ ‖x-0‖ < 2
  rw [sub_zero]
  constructor <;> linarith

theorem planeAnnulusOutput_subset : (planeAnnulusOutput (dim := dim)) ⊆ (planeAnnulus (dim := dim)) := by
  intro x hx
  change 4/5 < ‖x-0‖ ∧ ‖x-0‖ < 6/5 at hx
  constructor <;> linarith [hx.1,hx.2]

theorem norm_le_of_mem_closure_planeBall {r : ℝ} {x : (X dim)} (hx : x ∈ closure (planeBall normal r)) :
    ‖x‖ ≤ r + planeDepth := by
  have he : ‖(planeCenter normal)‖ = planeDepth := by
    simp [planeCenter,planeDepth,norm_smul,axis]
  have hDist := mem_closedBall.mp (closure_minimal ball_subset_closedBall isClosed_closedBall hx)
  have hNorm : ‖x-(planeCenter normal)‖ ≤ r := by simpa only [dist_eq_norm] using hDist
  have h := norm_add_le (x-(planeCenter normal)) (planeCenter normal)
  rw [sub_add_cancel,he] at h
  linarith

theorem height_le_of_mem_closure_planeBall {r : ℝ} {x : (X dim)} (hx : x ∈ closure (planeBall normal r)) :
    x normal ≤ r - planeDepth := by
  have hcenter : (planeCenter normal) normal = -planeDepth := by simp [planeCenter,axis,PiLp.smul_apply]
  have hDist := mem_closedBall.mp (closure_minimal ball_subset_closedBall isClosed_closedBall hx)
  have hNorm : ‖x-(planeCenter normal)‖ ≤ r := by simpa only [dist_eq_norm] using hDist
  have hCoord := (le_abs_self ((x-(planeCenter normal)) normal)).trans (PiLp.norm_apply_le (x-(planeCenter normal)) normal)
  simp only [PiLp.sub_apply,hcenter] at hCoord
  linarith

theorem height_le_of_mem_closure_planeAnnulusObservation {x : (X dim)}
    (hx : x ∈ closure (planeAnnulusObservation normal)) : x normal ≤ -(7/8) := by
  have hDist := mem_closedBall.mp (closure_minimal ball_subset_closedBall isClosed_closedBall hx)
  have hNorm : ‖x-(-(axis normal))‖ ≤ 1/8 := by simpa only [dist_eq_norm] using hDist
  have hCoord := (le_abs_self ((x-(-(axis normal))) normal)).trans (PiLp.norm_apply_le (x-(-(axis normal))) normal)
  simp [axis] at hCoord hNorm
  linarith

set_option maxHeartbeats 450000 in
/-- The two observed arms of the reference rooms meet the cross-series
exponent condition, uniformly near the Euclidean parameter. -/
theorem exists_planeReference_interpolation
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (p₀ : P) (g₁ g₂ : P → (MetricField dim))
    (hg₁ : ∀ p, SmoothMetric univ (g₁ p)) (hg₂ : ∀ p, SmoothMetric univ (g₂ p))
    (hb₁ : ∀ i j : (I dim), ContDiff ℝ ∞ (fun z : P × (X dim) => divergenceCoeff (g₁ z.1) z.2 i j))
    (hb₂ : ∀ i j : (I dim), ContDiff ℝ ∞ (fun z : P × (X dim) => divergenceCoeff (g₂ z.1) z.2 i j))
    (h₁ : g₁ p₀ = fun _ => (1 : (Mat dim))) (h₂ : g₂ p₀ = fun _ => (1 : (Mat dim))) :
    ∃ δ C₁ C₂ γ₁ γ₂ : ℝ, 0 < δ ∧ δ ≤ planeDepth/100 ∧
      0 < C₁ ∧ 0 < C₂ ∧ 0 < γ₂ ∧ γ₂ < 1 ∧ γ₁+γ₂ > 1 ∧
      ∃ (hS₁ : planeBall normal (planeDepth-δ) ⊆ planeBall normal (3*planeDepth))
        (hO₁ : planeBall normal (planeDepth+δ) ⊆ planeBall normal (3*planeDepth)),
      ∀ᶠ p in 𝓝 p₀,
        HarmonicInterpolation (isOpen_ball : IsOpen (planeBall normal (3*planeDepth)))
          (smoothMetric_restrict (hg₁ p) (subset_univ _)) hS₁ hO₁ C₁ γ₁ ∧
        HarmonicInterpolation (isOpen_openAnnulus 0 (1/2) 2)
          (smoothMetric_restrict (hg₂ p) (subset_univ _))
          (subset_closure.trans (closure_planeAnnulusObservation_subset (normal := normal)))
          (planeAnnulusOutput_subset (dim := dim)) C₂ γ₂ := by
  let K := closedAnnulus (0 : (X dim)) (3/4) (5/4)
  have hK : IsCompact K := isCompact_closedAnnulus 0 (3/4) (5/4)
  have hKD : K ⊆ (planeAnnulus (dim := dim)) := by
    intro x hx
    have ⟨hlo,hhi⟩ := mem_closedAnnulus.mp hx
    exact ⟨by linarith,by linarith⟩
  have hOK : (planeAnnulusOutput (dim := dim)) ⊆ K := by
    intro x hx
    change 4/5 < ‖x-0‖ ∧ ‖x-0‖ < 6/5 at hx
    exact mem_closedAnnulus.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hS : IsOpen (planeAnnulusObservation normal) := isOpen_ball
  have hSne : (planeAnnulusObservation normal).Nonempty := nonempty_ball.mpr (by norm_num)
  obtain ⟨C₂,γ₂,hC₂,hγ₂,hγ₂',hI₂⟩ := exists_connected_harmonicInterpolation g₂ p₀ hg₂ hb₂ h₂
    (isOpen_openAnnulus 0 (1/2) 2) (isConnected_openAnnulus 0 (1/2) 2 (by norm_num) (by norm_num))
    hS hSne (subset_closure.trans (closure_planeAnnulusObservation_subset (normal := normal))) hK hKD
  have hd : 0 < planeDepth := by norm_num [planeDepth]
  obtain ⟨δ,C₁,γ₁,hδ,hδsmall,hC₁,hγ₁,hγ₁',hI₁⟩ :=
    exists_nearOne_parameter_radial_interpolation g₁ p₀ hg₁ hb₁ h₁ (planeCenter normal) hd
      (show 1-γ₂ < 1 by linarith)
  have hS₁ : planeBall normal (planeDepth-δ) ⊆ planeBall normal (3*planeDepth) :=
    ball_subset_ball (by linarith)
  have hO₁ : planeBall normal (planeDepth+δ) ⊆ planeBall normal (3*planeDepth) :=
    ball_subset_ball (by linarith)
  refine ⟨δ,C₁,C₂,γ₁,γ₂,hδ,hδsmall,hC₁,hC₂,hγ₂,hγ₂',by linarith,hS₁,hO₁,?_⟩
  filter_upwards [hI₁,hI₂] with p hp₁ hp₂
  obtain ⟨_,_,hp₁⟩ := hp₁
  refine ⟨hp₁,fun q => ?_⟩
  exact (harmonicRestrict_norm_mono (isOpen_openAnnulus 0 (1/2) 2) _ hOK hKD q).trans (hp₂ q)

end CalderonN.FixedTube
