module

public import Proof.CalderonN.SmoothSphereRotation
public import Proof.CalderonN.SphereHarmonicBridge
import Mathlib.Tactic
public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.MetricConnection
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set Filter
namespace CalderonN
variable {N : ℕ}
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation

def frameVectorLinear (e : (Frame N)) (y : (X N)) : (X N) →L[ℝ] (X N) :=
  ∑ i,(EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (e y i)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end CalderonN
