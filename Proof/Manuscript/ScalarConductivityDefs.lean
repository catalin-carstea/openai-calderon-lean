module

public import Proof.CalderonPatch.Energy
public import Proof.Manuscript.Lemma81Defs

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPaper

open CalderonN (X)
open CalderonPatch

/-- The induced smooth domain model on the actual Euclidean closure.
The forward coordinate is inclusion and the inverse on the interior
is its restriction with values in the closure. The metric and volume
are the ones supplied by the Euclidean coordinate. -/
structure EuclideanClosure {n : ℕ} [NeZero n] (Ω : Set (X n))
    [ChartedSpace (EuclideanHalfSpace n) ↥(closure Ω)]
    [IsManifold (𝓡∂ n) ∞ ↥(closure Ω)] where
  regular_boundary : HasSmoothEuclideanBoundary Ω
  interior_iff (x : ↥(closure Ω)) : x ∈ (𝓡∂ n).interior ↥(closure Ω) ↔ (x : X n) ∈ Ω
  inclusion_smooth : ContMDiff (𝓡∂ n) 𝓘(ℝ, X n) ∞
    (Subtype.val : ↥(closure Ω) → X n)
  interiorInverse : X n → ↥(closure Ω)
  interiorInverse_apply (x : X n) (hx : x ∈ Ω) : (interiorInverse x : X n) = x
  interiorInverse_smooth : ContMDiffOn 𝓘(ℝ, X n) (𝓡∂ n) ∞ interiorInverse Ω
  metric : SmoothMetric n ↥(closure Ω)
  metric_inner (x : ↥(closure Ω)) (v w : TangentSpace (𝓡∂ n) x) :
    metric.inner x v w =
      inner ℝ
        (show X n from mfderiv (𝓡∂ n) 𝓘(ℝ, X n) (Subtype.val : ↥(closure Ω) → X n) x v)
        (show X n from mfderiv (𝓡∂ n) 𝓘(ℝ, X n) (Subtype.val : ↥(closure Ω) → X n) x w)
  volume : Measure ↥(closure Ω)
  volume_isMetricVolume : IsMetricVolume metric volume

namespace EuclideanClosure

variable {n : ℕ} [NeZero n] {Ω : Set (X n)}
  [ChartedSpace (EuclideanHalfSpace n) ↥(closure Ω)]
  [IsManifold (𝓡∂ n) ∞ ↥(closure Ω)]

theorem boundary_iff (D : EuclideanClosure Ω) (hΩ : IsOpen Ω) (x : ↥(closure Ω)) :
    x ∈ (𝓡∂ n).boundary ↥(closure Ω) ↔ (x : X n) ∈ frontier Ω := by
  change (𝓡∂ n).IsBoundaryPoint x ↔ (x : X n) ∈ frontier Ω
  rw [(𝓡∂ n).isBoundaryPoint_iff_not_isInteriorPoint]
  change (x ∉ (𝓡∂ n).interior ↥(closure Ω)) ↔ (x : X n) ∈ frontier Ω
  rw [D.interior_iff x, frontier, hΩ.interior_eq]
  exact ⟨fun h => ⟨x.property, h⟩, fun h => h.2⟩

/-- The identification of the manifold boundary with the Euclidean frontier. -/
def boundaryCoordinate (D : EuclideanClosure Ω) (hΩ : IsOpen Ω) :
    ↥((𝓡∂ n).boundary ↥(closure Ω)) → ↥(frontier Ω) :=
  fun p => ⟨p.val.val, (D.boundary_iff hΩ p.val).mp p.property⟩

end EuclideanClosure

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M] [MeasurableSpace M]

/-- The diagonal variational conductivity Dirichlet-to-Neumann pairing.
For the Euclidean metric and volume the integrand is γ times the
squared Euclidean gradient. Competitors share the prescribed trace. -/
def conductivityQuadraticEnergy (g : SmoothMetric n M) (μ : Measure M)
    (γ : M → ℝ) (f : M → ℝ) : ℝ :=
  sInf { c : ℝ | ∃ u : M → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ u ∧
    EqOn u f ((𝓡∂ n).boundary M) ∧
    c = ∫ x, γ x * covectorEnergy g x (mfderiv (𝓡∂ n) 𝓘(ℝ, ℝ) u x) ∂μ }

variable {Ω : Set (X n)}
  [ChartedSpace (EuclideanHalfSpace n) ↥(closure Ω)]
  [IsManifold (𝓡∂ n) ∞ ↥(closure Ω)]

/-- Equality of the scalar conductivity measurement on supported smooth
traces, written in the equivalent quadratic energy convention. -/
def ScalarPatchEnergyEqual (D : EuclideanClosure Ω) (hΩ : IsOpen Ω)
    (γ₁ γ₂ : X n → ℝ) (Γ : Set ↥(frontier Ω)) : Prop :=
  ∀ f : ↥(closure Ω) → ℝ, ContMDiff (𝓡∂ n) 𝓘(ℝ, ℝ) ∞ f →
    tsupport (fun p : ↥((𝓡∂ n).boundary ↥(closure Ω)) => f p) ⊆ D.boundaryCoordinate hΩ ⁻¹' Γ →
    conductivityQuadraticEnergy D.metric D.volume (γ₁ ∘ Subtype.val) f =
      conductivityQuadraticEnergy D.metric D.volume (γ₂ ∘ Subtype.val) f

end CalderonPaper
