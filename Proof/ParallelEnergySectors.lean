import Proof.PhysicalTruncatedNormComparison
import Proof.PhysicalScalarSelfNormComparison

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

/-- The complete first-base forward and genuine physical-adjoint self sector. -/
def firstSelfDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  metricDensity d.γ y *
    (‖P.firstCovariantCoreSection (fiveHalfToTwoSection U) y‖^2 -
      ‖P.firstFormalAdjointCore WF W U y‖^2)

/-- Keep both orientations of the scalar-second/first-base cross term together. -/
def scalarFirstDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2 * metricDensity d.γ y *
    (⟪scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius)
        (fiveHalfToTwoSection U) y,
      P.firstCovariantCoreSection (fiveHalfToTwoSection U) y⟫_ℝ -
    ⟪scalarCovariantSecondTransposeSection d (metricDensity d.γ)
        (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U) y,
      P.firstFormalAdjointCore WF W U y⟫_ℝ)

def firstSelfComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y +
    firstSelfDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def scalarFirstComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  scalarFirstDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y +
    scalarFirstDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

end ShrinkingSpheres.ParallelEnergy
