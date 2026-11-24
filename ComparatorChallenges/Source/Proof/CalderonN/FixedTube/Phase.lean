module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
public import Proof.CalderonN.Coordinates

/-!
Adapted from `Calderon/MixedKernelConstruction/MixedKernelClosedTubeConstruction.lean`
in `anisotropic-calderon-lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc.
These are the fixed-separation tube calculations used in Theorem 3.1.
-/

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped InnerProductSpace Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} {normal : I dim}

/-- Pairing of the coordinates perpendicular to the selected normal axis. -/
def transversePair (normal : I dim) (u v : X dim) : ℝ :=
  ∑ i ∈ Finset.univ.erase normal, u i * v i

/-- The tube height uses the squared norm of the transverse coordinates. -/
def tubeHeight (normal : I dim) (M e0 : ℝ) (Y : X dim) : ℝ :=
  M + Y normal + e0 * transversePair normal Y Y

end CalderonN.FixedTube
