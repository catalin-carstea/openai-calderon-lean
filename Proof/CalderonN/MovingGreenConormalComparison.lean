module

public import Proof.CalderonN.MovingGreenFluxDensity
public import Proof.CalderonN.ScaledGreenDatumJets
public import Proof.CalderonN.UniformBallConormalDifference

import Proof.CalderonN.FixedBallPoissonCongruence
import Mathlib.Tactic

/-! Adapted from `MovingGreenConormalComparison` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 3100000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def normalGreenMetric (g : ℝ → (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim))
    (q : (NormalGreenParameter dim) × (X dim)) : (Mat dim) :=
  normalizedBallMetric (g q.1.1) (E q.1.1) (e q.1.1) q.1.2.1 q.1.2.2 q.2

@[expose] def normalGreenAngularLift (γ : (MetricField dim)) (e : (Frame dim)) (lam : ℝ) (r : (X dim) → ℝ)
    (q : (X dim) × (X dim)) : (NormalGreenParameter dim) × (X dim) :=
  ((lam,(q.1,r q.1)),(movingBallToFrame γ e q).2)

theorem contDiff_normalGreenAngularLift {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) (lam : ℝ)
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (normalGreenAngularLift γ e lam r) :=
  (contDiff_const.prodMk (contDiff_fst.prodMk (hr.comp contDiff_fst))).prodMk
    (contDiff_movingBallToFrame hγ he).snd

theorem normalGreenAngularLift_frame {γ : (MetricField dim)} {e : (Frame dim)} {lam : ℝ}
    {r : (X dim) → ℝ} {y : (X dim)} {w : (X dim)}
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0) :
    normalGreenAngularLift γ e lam r (y,frameVector e y w) = ((lam,(y,r y)),w) := by
  change ((lam,(y,r y)),(movingBallToFrame γ e (movingBallFromFrame e (y,w))).2) = _
  rw [movingBallToFrame_fromFrame he]

/-- With the radius held fixed on each angular slice, the literal Green
flux density equals area times the conormal difference of the
radius-normalized boundary value. -/
theorem movingGreenFluxDensity_eq_ballConormalDifference
    {γ g : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    (lam : ℝ) (r : (X dim) → ℝ) (G : (X dim) × (X dim) → ℝ) (q : (X dim) × (X dim))
    {U : Set (X dim)} (hU : IsOpen U) (hCU : closedBall (0 : (X dim)) 1 ⊆ U)
    (hg : SmoothMetric U (fun z => movingBallMetric (g lam) (E lam) (e lam) r (q.1,z)))
    (hd : smoothNear (fun z => framedMovingGreenKernel (E lam) (e lam) r G (q.1,z)) (standardSphere dim))
    (hw : (movingBallToFrame (γ lam) (e lam) q).2 ≠ 0) :
    movingGreenFluxDensity (γ lam) (g lam) (E lam) (e lam) r G q =
      (unitSphereArea dim) * ballConormalDifference (normalGreenMetric g E e) (scaledNormalGreenDatum E e G)
        (normalGreenAngularLift (γ lam) (e lam) lam r q) := by
  let y := q.1
  let w := sphereNormalize (movingBallToFrame (γ lam) (e lam) q).2
  let a := fun z => movingBallMetric (g lam) (E lam) (e lam) r (y,z)
  let d := fun z => framedMovingGreenKernel (E lam) (e lam) r G (y,z)
  let u := fixedBallPoisson a d
  have hw' : w ∈ (standardSphere dim) := sphereNormalize_mem_sphere hw
  have hu : FixedBallSolution a d u := fixedBallPoisson_solution hU hCU hg hd
  have huR := hu.const_mul ((r y)^(dim-2))
  have hD := fixedBallPoisson_fderiv_eq_of_solution hU hCU hg huR (fun z (_ : z ∈ (standardSphere dim)) => rfl)
  obtain ⟨T,hT,hST,hTd⟩ := hd
  have hdW := (hTd.contDiffAt (hT.mem_nhds (hST hw'))).differentiableAt (by simp)
  have hV := fderiv_const_mul hdW ((r y)^(dim-2))
  have hUder := fderiv_const_mul (hu.1.differentiable (by simp) w) ((r y)^(dim-2))
  have hD' := hD (sphere_subset_closedBall hw')
  change (unitSphereArea dim)*((r y)^(dim-2)*(ballConormal a u w-ballConormal a d w)) =
    (unitSphereArea dim)*(ballConormal a (fixedBallPoisson a (fun z => (r y)^(dim-2)*d z)) w-
      ballConormal a (fun z => (r y)^(dim-2)*d z) w)
  simp only [ballConormal_eq_fderiv_conormalVector]
  rw [hD',hUder,hV]
  simp only [smul_apply,smul_eq_mul]
  ring

end CalderonN
