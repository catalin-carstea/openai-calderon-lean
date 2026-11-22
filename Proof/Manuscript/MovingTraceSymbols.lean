module

public import Proof.CalderonN.ActualGreenTransfer
public import Mathlib.Geometry.Manifold.Instances.Sphere

@[expose] public section

noncomputable section

open CalderonN MeasureTheory Metric Set
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

abbrev AngularCoordinates (dim : ℕ) := X (dim - 1)
abbrev SphereOperator (dim : ℕ) := (X dim → ℂ) → X dim → ℂ
abbrev LocalAngularSymbol (P : Type) (dim : ℕ) :=
  P → X dim → AngularCoordinates dim → AngularCoordinates dim → ℂ

/-- Bounds for all angular symbol seminorms at each of the first six base
derivative orders, uniformly over the family of radii. -/
def SymbolSeminormBounds {P : Type} {dim : ℕ}
    (Y : Set (X dim)) (β : P → X dim → ℝ) (order : ℤ)
    (a : LocalAngularSymbol P dim) : Prop :=
  ∀ j k l : ℕ, j ≤ 6 →
    ∃ C : ℝ, 0 < C ∧ ∀ t y, y ∈ Y → ∀ x ξ : AngularCoordinates dim,
      ‖iteratedFDeriv ℝ j (fun b =>
          iteratedFDeriv ℝ k (fun x' =>
            iteratedFDeriv ℝ l (a t b x') ξ) x) y‖ ≤
        C * (β t y) ^ j * (1 + ‖ξ‖) ^ ((order : ℝ) - l)

/-- Classical symbols have smooth homogeneous coefficients and a remainder
of order `m-N` after subtracting the first `N` homogeneous terms with a
fixed cutoff at zero. -/
def UniformClassicalAngularSymbol {P : Type} {dim : ℕ}
    (Y : Set (X dim)) (β : P → X dim → ℝ) (order : ℤ)
    (a : LocalAngularSymbol P dim) : Prop :=
  (∀ t, ContDiffOn ℝ ∞ (fun q : X dim × (AngularCoordinates dim × AngularCoordinates dim) =>
    a t q.1 q.2.1 q.2.2) (Y ×ˢ univ)) ∧
  SymbolSeminormBounds Y β order a ∧
  ∃ (χ : AngularCoordinates dim → ℝ) (h : ℕ → LocalAngularSymbol P dim),
    ContDiff ℝ ∞ χ ∧ (∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0) ∧ (∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 1) ∧
    (∀ j t, ContDiffOn ℝ ∞
      (fun q : X dim × (AngularCoordinates dim × AngularCoordinates dim) => h j t q.1 q.2.1 q.2.2)
      (Y ×ˢ (univ ×ˢ ({0}ᶜ : Set (AngularCoordinates dim))))) ∧
    (∀ j t y, y ∈ Y → ∀ x ξ, ξ ≠ 0 → ∀ ρ : ℝ, 0 < ρ →
      h j t y x (ρ • ξ) = ((ρ ^ ((order : ℝ) - j) : ℝ) : ℂ) * h j t y x ξ) ∧
    ∀ N : ℕ, SymbolSeminormBounds Y β (order - (N : ℤ))
      (fun t y x ξ => a t y x ξ - (χ ξ : ℂ) * ∑ j ∈ Finset.range N, h j t y x ξ)

/-- Positive Fourier phase in the Euclidean stereographic coordinates. -/
def angularFourierPhase {dim : ℕ} (x ξ : AngularCoordinates dim) : ℂ :=
  Complex.exp (((2 * Real.pi * ⟪x, ξ⟫_ℝ : ℝ) : ℂ) * Complex.I)

def angularFourierTransform {dim : ℕ} (f : AngularCoordinates dim → ℂ)
    (ξ : AngularCoordinates dim) : ℂ :=
  ∫ x, angularFourierPhase (-x) ξ * f x

/-- Support of an angular cutoff on the sphere itself. -/
def angularSupport {dim : ℕ} (χ : X dim → ℂ) : Set ↥(standardSphere dim) :=
  closure {w | χ w ≠ 0}

/-- Bounds for the smooth kernels of operators localized to disjoint angular
supports. Ambient extensions are used to express angular derivatives. -/
def UniformAngularSmoothing {P : Type} {dim : ℕ}
    (Y : Set (X dim)) (β : P → X dim → ℝ)
    (K : P → X dim → X dim → X dim → ℂ) : Prop :=
  (∀ t, smoothNear (fun q : X dim × (X dim × X dim) => K t q.1 q.2.1 q.2.2)
    (Y ×ˢ (standardSphere dim ×ˢ standardSphere dim))) ∧
  ∀ j k l : ℕ, j ≤ 6 → ∃ C : ℝ, 0 < C ∧
    ∀ t y, y ∈ Y → ∀ w z : ↥(standardSphere dim),
      ‖iteratedFDeriv ℝ j (fun b =>
        iteratedFDeriv ℝ k (fun w' => iteratedFDeriv ℝ l (K t b w') z.val) w.val) y‖ ≤
        C * (β t y) ^ j

/-- Classical pseudodifferential families on the compact unit sphere.
Localization in each stereographic chart is exactly a quantized classical
symbol, and localization to disjoint supports has a smooth kernel. -/
def UniformClassicalSphereOperator {P : Type} {dim : ℕ}
    [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]
    (Y : Set (X dim)) (β : P → X dim → ℝ) (order : ℤ)
    (A : P → X dim → SphereOperator dim) : Prop :=
  (∀ v : ↥(standardSphere dim),
    let κ := stereographic' (dim - 1) v
    ∀ χ η : X dim → ℂ, smoothNear χ (standardSphere dim) → smoothNear η (standardSphere dim) →
      angularSupport χ ⊆ κ.source → angularSupport η ⊆ κ.source →
      ∃ a : LocalAngularSymbol P dim, UniformClassicalAngularSymbol Y β order a ∧
        ∀ t y, y ∈ Y → ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
          ∀ x ∈ κ.target,
            let localizedDatum := fun z : AngularCoordinates dim => η (κ.symm z) * u (κ.symm z)
            let integrand := fun ξ : AngularCoordinates dim =>
              angularFourierPhase x ξ * a t y x ξ * angularFourierTransform localizedDatum ξ
            Integrable localizedDatum ∧ Integrable integrand ∧
              χ (κ.symm x) * A t y (fun w => η w * u w) (κ.symm x) =
                ∫ ξ, integrand ξ) ∧
  ∀ χ η : X dim → ℂ, smoothNear χ (standardSphere dim) → smoothNear η (standardSphere dim) →
    Disjoint (angularSupport χ) (angularSupport η) →
    ∃ K : P → X dim → X dim → X dim → ℂ, UniformAngularSmoothing Y β K ∧
      ∀ t y, y ∈ Y → ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
        ∀ w : ↥(standardSphere dim),
          χ w * A t y (fun z => η z * u z) w =
            ∫ z : ↥(standardSphere dim), K t y w z * u z ∂(sphereProbability dim)

/-- The sphere adjoint of differentiating the flat Dirichlet solution
along the given velocity. Constant velocities give the adjoints of the
ambient derivatives. The radial velocity gives the self-adjoint operator
whose eigenvalue on a degree-`k` harmonic is `k`. -/
def flatAngularVelocityAdjoint {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
    (V : X dim → X dim) : SphereOperator dim :=
  fun φ w =>
    let g : X dim × X dim → Mat dim := fun _ => 1
    let W : X dim × X dim → X dim := fun q => V q.2
    ⟨parametricBallVelocityAdjoint g W (fun q => (φ q.2).re) (0,w),
      parametricBallVelocityAdjoint g W (fun q => (φ q.2).im) (0,w)⟩

/-- All smooth positive profiles meeting the fixed normal radius, logarithmic
profile, and coefficient smallness conditions of the moving trace problem. -/
def AdmittedTraceRadius {dim : ℕ} (Y : Set (X dim))
    (γ g₂ : MetricField dim) (e : Frame dim) (ρ floor c₀ ε : ℝ) (Cj : Fin 9 → ℝ)
    (r : X dim → ℝ) : Prop :=
  ContDiff ℝ ∞ r ∧ Profile Y γ e r floor c₀ Cj ∧ Small Y γ g₂ r ε ∧
    ∀ y ∈ Y, r y < ρ

end CalderonPaper
