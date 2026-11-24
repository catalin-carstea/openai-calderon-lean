module

public import Proof.CalderonN.CompactParameterSmoothness
public import Proof.CalderonN.SphereHarmonicBridge
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates

@[expose] public section

/- Adopted from the selected ZIP, lean/Calderon/SmoothSphereFields.lean.
   Mathematical declarations and proof bodies are preserved; local imports are rewritten. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.SmoothSphereFields
variable {N : ℕ} [NeZero N]
open SphereHarmonic CompactParameterSmoothness

def unitSphereInclusion : C((UnitSphere N),(CalderonN.X N)) := ⟨Subtype.val,continuous_subtype_val⟩

def ambientSphereSection (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) :
    (CalderonN.X N) → C((UnitSphere N),ℝ) := compactPullback G hG.continuous unitSphereInclusion

def ambientSphereL2 (G : (CalderonN.X N) × (CalderonN.X N) → ℝ) (hG : ContDiff ℝ ∞ G) : (CalderonN.X N) → (SphereL2 N) :=
  fun x => ContinuousMap.toLp 2 (unitSphereProbability N) ℝ (ambientSphereSection G hG x)

end OAI.AnisotropicCalderon.SmoothSphereFields
