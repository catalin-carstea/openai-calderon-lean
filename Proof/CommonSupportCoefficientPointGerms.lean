import Proof.NormalizedFirstCoefficientTaylor
import Proof.Archive.CommonSupportMatrixInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- A joint compact representative has the expected point coefficient germs
    on each fixed parameter slice. -/
theorem commonSupport_coefficient_point_germs
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A B : P × X → Mat) (hA : ContDiff ℝ ∞ A)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
    (x : P) (f : X → Mat)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (x,z)] B)
    (hSlice : ∀ w,B (x,w) = f w) :
    ∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (commonSupportMatrixFamily 2 A hA S hS hz x i j) =ᶠ[𝓝 z]
        (fun w => f w i j) := by
  intro z hzB i j
  have hInput : ContinuousAt (fun w : X => (x,w)) z := continuousAt_const.prodMk continuousAt_id
  have hNear := (hRep z hzB).comp_tendsto hInput
  filter_upwards [hNear] with w hw
  have hValue := congrArg (fun G : X → Mat => G w i j)
    (coefficientMatrixField_commonSupportMatrixFamily 2 A hA S hS hz x)
  exact hValue.trans ((congrArg (fun C : Mat => C i j) hw).trans
    (congrArg (fun C : Mat => C i j) (hSlice w)))

end ShrinkingSpheres
