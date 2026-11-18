import Proof.PullbackCoefficientRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Compact coefficient jets representing any smooth local matrix field. -/
theorem exists_local_coefficient_representative (a : MetricField)
    (ha : ContDiffOn ℝ ∞ a (Metric.ball (0:X) 3)) (r : ℕ) :
    ∃ F : SmoothCoefficientMatrix r,∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue r (F i j) =ᶠ[𝓝 x] (fun z => a z i j) := by
  have h23 : Metric.closedBall (0:X) 2 ⊆ Metric.ball (0:X) 3 := by
    intro x hx
    change dist x 0 < 3
    change dist x 0 ≤ 2 at hx
    linarith
  obtain ⟨A,hA,hAc,hNear⟩ := exists_contDiff_eq_near_compact_of_contDiffOn
    (Metric.closedBall (0:X) 2) (Metric.ball (0:X) 3) (isCompact_closedBall _ _)
    Metric.isOpen_ball h23 a ha
  have hEntry (i j : I) : ContDiff ℝ ∞ (fun x => A x i j) :=
    contDiff_pi.mp (contDiff_pi.mp hA i) j
  have hCompact (i j : I) : HasCompactSupport (fun x => A x i j) :=
    hAc.comp_left (g:=fun Q : Mat => Q i j) rfl
  refine ⟨fun i j => compactCoefficient r (fun x => A x i j) (hEntry i j) (hCompact i j),?_⟩
  intro x hx i j
  rw [coefficientValue_compactCoefficient]
  filter_upwards [hNear x hx] with z hz
  exact congrArg (fun Q : Mat => Q i j) hz

/-- The scalar affine coefficient model has actual compact jet representatives. -/
theorem exists_linear_scalar_coefficient (L : X →L[ℝ] ℝ) (r : ℕ) :
    ∃ F : SmoothCoefficientMatrix r,∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue r (F i j) =ᶠ[𝓝 x] (fun z => L z*(1:Mat) i j) := by
  apply exists_local_coefficient_representative (fun z => L z • (1:Mat)) _ r
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact L.contDiff.contDiffOn.mul contDiffOn_const

end ShrinkingSpheres
