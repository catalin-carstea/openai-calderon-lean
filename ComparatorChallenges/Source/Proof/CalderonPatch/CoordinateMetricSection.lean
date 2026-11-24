module

public import Proof.CalderonPatch.NativeNormalChart
public import Proof.CalderonN.MetricConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Riemannian
public import Proof.CalderonN.Coordinates

@[expose] public section

noncomputable section
open Bundle ContinuousLinearMap Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X MetricField metricBilinear)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "T" => TangentSpace J
local notation "B" => (X n →L[ℝ] X n →L[ℝ] ℝ)
local notation "JB" => (ModelWithCorners.prod J 𝓘(ℝ, B))

/-- A coordinate matrix field pulled back to the native tangent
bundle by the derivative of a smooth coordinate map. -/
def nativeCoordinateBilinear (γ : MetricField n) (q : M → X n) (x : M) :
    T x →L[ℝ] T x →L[ℝ] ℝ := by
  let D : X n →L[ℝ] X n := mfderiv J K q x
  exact (metricBilinear γ (q x)).bilinearComp D D

end CalderonPatch
