module

public import Proof.CalderonN.SphereHarmonicBridge
import Mathlib.Tactic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Proof.CalderonN.ZonalProjection
public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum
public import Proof.CalderonN.Coordinates

public section

/- The Hilbert sum argument follows SphereHilbertDecomposition and
   LegendreHilbert from Proposition 5.3 check f308cb9d. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace CalderonN
open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

theorem isHilbertSum_harmonicSphereSubspaces :
    IsHilbertSum ℝ (fun k : ℕ => ↥(harmonicSphereSubspace n k))
      (fun k => (harmonicSphereSubspace n k).subtypeₗᵢ) := sorry

def sphereHarmonicDecomposition :
    SphereL2 n ≃ₗᵢ[ℝ] lp (fun k : ℕ => harmonicSphereSubspace n k) 2 :=
  isHilbertSum_harmonicSphereSubspaces.linearIsometryEquiv

end CalderonN
