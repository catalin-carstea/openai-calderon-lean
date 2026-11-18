import Proof.PullbackDirichletCoefficient
import Proof.Archive.CoefficientMatrixRegularity
import Proof.Archive.FiniteDimensionalLocalSmoothExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- A compact coefficient-jet representative of the actual local coefficient,
    agreeing as a smooth germ throughout the closed regularity neighborhood.
    No bound is asserted for its arbitrary exterior extension. -/
theorem Elliptic.exists_coefficient_representative {K : ℝ} {H : MetricField}
    (hEll : Elliptic (Metric.closedBall (0:X) 3) K H) (hK : 0 < K) (r : ℕ) :
    ∃ F : SmoothCoefficientMatrix r,∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue r (F i j) =ᶠ[𝓝 x] (fun z => principalCoefficient H z i j) := by
  have hSmooth : ContDiffOn ℝ ∞ (principalCoefficient H) (Metric.ball (0:X) 3) :=
    (hEll.contDiffOn_principalCoefficient hK).mono Metric.ball_subset_closedBall
  have h23 : Metric.closedBall (0:X) 2 ⊆ Metric.ball (0:X) 3 := by
    intro x hx
    change dist x 0 < 3
    change dist x 0 ≤ 2 at hx
    linarith
  obtain ⟨A,hA,hAc,hNear⟩ := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.closedBall (0:X) 2) (Metric.ball (0:X) 3) (isCompact_closedBall _ _)
    Metric.isOpen_ball h23 (principalCoefficient H) hSmooth
  have hEntry (i j : I) : ContDiff ℝ ∞ (fun x => A x i j) :=
    contDiff_pi.mp (contDiff_pi.mp hA i) j
  have hCompact (i j : I) : HasCompactSupport (fun x => A x i j) :=
    hAc.comp_left (g:=fun Q : Mat => Q i j) rfl
  let F : SmoothCoefficientMatrix r := fun i j =>
    compactCoefficient r (fun x => A x i j) (hEntry i j) (hCompact i j)
  refine ⟨F,?_⟩
  intro x hx i j
  change coefficientValue r (compactCoefficient r (fun z => A z i j) (hEntry i j) (hCompact i j)) =ᶠ[𝓝 x] _
  rw [coefficientValue_compactCoefficient]
  filter_upwards [hNear x hx] with z hz
  exact congrArg (fun Q : Mat => Q i j) hz

lemma coefficientValue_sub_local (r : ℕ) (F G : SmoothCoefficientJets r) :
    coefficientValue r (F-G) = coefficientValue r F-coefficientValue r G := by
  funext x
  rfl

/-- The compact representative and a flat center share exactly the local
    coefficient difference germ needed by the sharp strong-operator estimate. -/
theorem coefficient_difference_germ {a : X → Mat} (F F0 : SmoothCoefficientMatrix 2) (c : ℝ)
    (hRep : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j))
    (hFlat : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    {x : X} (hx : x ∈ (ballOpens : Set X)) (i j : I) :
    coefficientValue 2 ((F-c • F0) i j) =ᶠ[𝓝 x] (fun z => a z i j-c*(1:Mat) i j) := by
  have hx2 : x ∈ Metric.ball (0:X) 2 := by
    have hh : ‖x‖ < 1 := by simpa only [coe_ballOpens,OAI.AnisotropicCalderon.B,Metric.mem_ball,dist_zero_right] using hx
    change dist x 0 < 2
    rw [dist_zero_right]
    linarith
  have hFlatNear : coefficientValue 2 (F0 i j) =ᶠ[𝓝 x] (fun _ => (1:Mat) i j) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx2] with z hz
    exact congrArg (fun Q : Mat => Q i j) (hFlat z (Metric.ball_subset_closedBall hz))
  have hPoint := hRep x (Metric.ball_subset_closedBall hx2) i j
  filter_upwards [hPoint,hFlatNear] with z hz hz0
  change coefficientValue 2 (F i j-c • F0 i j) z = _
  rw [coefficientValue_sub_local,coefficientValue_smul]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hz,hz0]

end ShrinkingSpheres
