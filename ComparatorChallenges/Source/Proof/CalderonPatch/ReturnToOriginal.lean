module

public import Proof.CalderonPatch.MatchedCoordinates
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Proof.CalderonN.Coordinates
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Proof.CalderonPatch.Energy

public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M N₁ N₂ : Type*}
  [TopologicalSpace M] [CompactSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) ∞ M]
  [TopologicalSpace N₁] [T2Space N₁] [ChartedSpace (EuclideanHalfSpace n) N₁]
  [IsManifold (𝓡∂ n) ∞ N₁]
  [TopologicalSpace N₂] [T2Space N₂] [ChartedSpace (EuclideanHalfSpace n) N₂]
  [IsManifold (𝓡∂ n) ∞ N₂]

local notation "J" => 𝓡∂ n

/-- An original manifold embedded in its attached extension. Removing
the closure of the open cap from the extended interior leaves exactly
the image of the original interior. -/
structure OriginalCopy {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]
    [IsManifold (𝓡∂ n) ∞ N] (g : SmoothMetric n M) (gExt : SmoothMetric n N) (cap : Set N) where
  embed : M → N
  inverse : N → M
  left_inv : Function.LeftInverse inverse embed
  smooth : ContMDiff J J ∞ embed
  smooth_inverse : ContMDiffOn J J ∞ inverse (range embed)
  interior_image : embed '' (J).interior M = (J).interior N \ closure cap
  metric : ∀ p (v w : TangentSpace J p), g.inner p v w =
    gExt.inner (embed p) (mfderiv J J embed p v) (mfderiv J J embed p w)

end CalderonPatch
