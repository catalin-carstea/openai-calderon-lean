module

public import Proof.CalderonN.FixedBallMetricEllipticity
public import Proof.CalderonN.CompactSmoothExtension
public import Proof.CalderonN.NormalDirichlet

public import Proof.CalderonN.ClassicalBallDirichlet
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricDivergence
import Proof.CalderonN.FramePullback
import Proof.CalderonN.EllipticCalculus
import Mathlib.Tactic

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim]



/-- The actual chart Laplacian and the fixed inverse have the same
classical equation after multiplying by the positive volume density. -/
theorem negativeBallDivergence_eq_neg_laplace {S : Set (X dim)} (hS : IsOpen S)
    {g : (MetricField dim)} (hg : SmoothMetric S g) {a : (X dim) → (Mat dim)}
    (ha : ∀ x ∈ S, ∀ i j, a x i j = divergenceCoeff g x i j)
    {b : (X dim) → ℝ} (hb : ContDiffOn ℝ ∞ b S) {x : (X dim)} (hx : x ∈ S) :
    negativeBallDivergence a b x = -(chartVolume g x * laplace g b x) := by
  rw [chartVolume_mul_laplace_eq_divergence hS hg hb hx]
  unfold negativeBallDivergence Elliptic.Lop Elliptic.pd
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply eqOn_coordDeriv hS _ i hx
  intro z hz
  simp only [divergenceFlux,ha z hz]

set_option maxHeartbeats 1600000 in
/-- The Dirichlet solution for a smooth metric defined around the closed
unit ball. The coefficients are cut off only outside a neighborhood
of the ball, so the strong inverse solves the original equation there. -/
theorem exists_classical_fixedBallDirichlet [Nontrivial (Fin dim)]
    {S : Set (X dim)} (hS : IsOpen S) (hC : closedBall (0 : (X dim)) 1 ⊆ S)
    {g : (MetricField dim)} (hg : SmoothMetric S g)
    {d : (X dim) → ℝ} (hd : smoothNear d (standardSphere dim)) :
    ∃ b : (X dim) → ℝ, ContDiff ℝ ∞ b ∧ EqOn b d (standardSphere dim) ∧
      ∀ x ∈ ball (0 : (X dim)) 1, laplace g b x = 0 := by
  let A (x : (X dim)) : (Mat dim) := fun i j => divergenceCoeff g x i j
  have hA : ContDiffOn ℝ ∞ A S := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact contDiffOn_divergenceCoeff hg i j
  obtain ⟨a,ha,haK,V,hV,hCV,hVS,haV⟩ :=
    exists_contDiff_extension_near_compact hS (isCompact_closedBall (0 : (X dim)) 1) hC hA
  obtain ⟨lam,Lam,hEll⟩ := exists_uniformEllipticOn_fixedBall a ha.continuous (by
    intro x hx
    rw [haV (hCV hx)]
    exact divergenceMatrix_posDef g x (hg.2 x (hC hx)))
  obtain ⟨W,hW,hWsub,hdW⟩ := hd
  obtain ⟨D,hD,_,T,_,hST,_,heD⟩ := exists_contDiff_extension_near_compact hW
    (isCompact_sphere (0 : (X dim)) 1) hWsub hdW
  let a' (q : ℝ × (X dim)) := a q.2
  let D' (q : ℝ × (X dim)) := D q.2
  have hSupp (p : ℝ) (z : (X dim)) (hz : z ∉ tsupport a) : a' (p,z) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := a) hz
  obtain ⟨b,hb,hbd,hbe⟩ :=
    exists_classical_ballDirichlet_of_parametricStrongSolution (univ : Set ℝ) a'
      (ha.comp contDiff_snd) (tsupport a) haK.isCompact hSupp D' (hD.comp contDiff_snd)
      (fun _ => lam) (fun _ => Lam) (fun _ _ => hEll) 0 (mem_univ _)
  refine ⟨b,hb,fun w hw => (hbd hw).trans (heD (hST hw)),fun x hx => ?_⟩
  let B := ball (0 : (X dim)) 1
  have hB : B ⊆ V := ball_subset_closedBall.trans hCV
  have hLap := negativeBallDivergence_eq_neg_laplace hV
    ⟨fun i j => (hg.1 i j).mono hVS,fun x hx => hg.2 x (hVS hx)⟩
    (fun z hz i j => congrArg (fun M : (Mat dim) => M i j) (haV hz)) hb.contDiffOn (hB hx)
  have hZero : negativeBallDivergence a b x = 0 := hbe hx
  rw [hZero] at hLap
  exact (mul_eq_zero.mp (neg_eq_zero.mp hLap.symm)).resolve_left
    (Real.sqrt_pos.mpr (hg.2 x (hC (ball_subset_closedBall hx))).det_pos).ne'

/-- Existence and uniqueness in the frozen Dirichlet interface, now for
the literal normal charts and the original first metric. -/
theorem normalDirichlet_of_metric [Nontrivial (Fin dim)]
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X dim) → ℝ} (hr : ∀ y ∈ Y, 0 < r y ∧ r y < ρ) :
    Dirichlet Y γ g E r := by
  apply normalDirichlet_of_fixedBall hΩ hg hE hN he hr
  intro y hy d hd
  let F := normalBallChartMap E e y (r y)
  obtain ⟨h₁,hMap,hD⟩ := normalBallChartMap_on_openBall hE hN hy (he y hy) (hr y hy).1
  have hC : closedBall (0 : (X dim)) 1 ⊆ ball (0 : (X dim)) (ρ/(r y)) :=
    closedBall_subset_ball ((lt_div_iff₀ (hr y hy).1).mpr (by simpa using (hr y hy).2))
  have hMetric : SmoothMetric (ball (0 : (X dim)) (ρ/r y)) (pullbackMetric g F) :=
    smoothMetric_pullbackMetric hg (contDiff_normalBallChartMap hE e y (r y)) hMap
      (fun z hz => coordinateJacobian_det_ne_zero (hD z hz))
  obtain ⟨b,hb,hD,hLap⟩ := exists_classical_fixedBallDirichlet isOpen_ball hC hMetric hd
  exact ⟨b,⟨univ,isOpen_univ,subset_univ _,hb.contDiffOn⟩,hD,hLap⟩

end CalderonN
