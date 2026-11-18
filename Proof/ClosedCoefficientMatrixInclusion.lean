import Proof.Archive.ClosedCoefficientJets
import Proof.Archive.CommonSupportMatrixInverse
import Mathlib.Topology.NhdsWithin
import Proof.MatrixFieldJetNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

abbrev ClosedCoefficientMatrix (r : ℕ) := I → I → ClosedCoefficientJets r

def smoothCoefficientMatrixClosureInclusionL (r : ℕ) :
    SmoothCoefficientMatrix r →L[ℝ] ClosedCoefficientMatrix r :=
  ContinuousLinearMap.piMap (fun _ : I =>
    ContinuousLinearMap.piMap (fun _ : I => smoothCoefficientClosureInclusionL r))

lemma norm_smoothCoefficientMatrixClosureInclusionL (r : ℕ) (F : SmoothCoefficientMatrix r) :
    ‖smoothCoefficientMatrixClosureInclusionL r F‖ = ‖F‖ := rfl

lemma isometry_smoothCoefficientMatrixClosureInclusionL (r : ℕ) :
    Isometry (smoothCoefficientMatrixClosureInclusionL r) := fun _ _ => rfl

theorem denseRange_smoothCoefficientMatrixClosureInclusionL (r : ℕ) :
    DenseRange (smoothCoefficientMatrixClosureInclusionL r) := by
  exact DenseRange.piMap (fun _ : I =>
    DenseRange.piMap (fun _ : I => denseRange_smoothCoefficientClosureInclusionL r))

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def commonSupportClosedCoefficientMatrixFamily (r : ℕ) (a : P × X → Mat) (ha : ContDiff ℝ ∞ a)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p : P) :
    ClosedCoefficientMatrix r :=
  smoothCoefficientMatrixClosureInclusionL r (commonSupportMatrixFamily r a ha S hS hz p)

theorem contDiff_commonSupportClosedCoefficientMatrixFamily (r : ℕ)
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) :
    ContDiff ℝ ∞ (commonSupportClosedCoefficientMatrixFamily r a ha S hS hz) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_commonSupportClosedCoefficientFamily r (fun v => a v i j)
    (contDiff_pi.mp (contDiff_pi.mp ha i) j) S hS (fun p z h => by rw [hz p z h];rfl)

end ShrinkingSpheres
