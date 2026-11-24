module

public import Proof.CalderonN.Coordinates
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/- Port of the normal ball and trace definitions from the checked 3D Theorem 3.1 packet
   (55d37bfe), Proof/LocalMetricExtension/Coercivity.lean, and its Proposition 5.3 source. -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators

namespace CalderonN

variable {n : ℕ}

def sphereAt (γ : MetricField n) (y : X n) : Set (X n) := {v | metricPair γ y v v = 1}

def disk (γ : MetricField n) (y : X n) (s : ℝ) : Set (X n) := {v | metricPair γ y v v ≤ s^2}

def smoothNear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (s : Set E) : Prop :=
  ∃ V, IsOpen V ∧ s ⊆ V ∧ ContDiffOn ℝ ∞ f V

def bundle (Y : Set (X n)) (γ : MetricField n) : Set (X n × X n) :=
  {p | p.1 ∈ Y ∧ p.2 ∈ sphereAt γ p.1}

/-- A smooth system of normal coordinates about every center, specified by its geodesic IVP. -/
def NormalCoordinates (Y Ω : Set (X n)) (γ : MetricField n) (expMap : X n × X n → X n)
    (radius : X n → ℝ) : Prop :=
  let tube : Set (X n × X n) := {p | p.1 ∈ Y ∧ p.2 ∈ disk γ p.1 (radius p.1)}
  smoothNear expMap tube ∧ ∀ y ∈ Y,
    0 < radius y ∧
    InjOn (fun v => expMap (y,v)) (disk γ y (radius y)) ∧
    ∀ v ∈ disk γ y (radius y),
      expMap (y,v) ∈ Ω ∧
      Function.Bijective (fderiv ℝ (fun w => expMap (y,w)) v) ∧
      let path := fun t : ℝ => expMap (y,t • v)
      path 0 = y ∧ deriv path 0 = v ∧ ∀ t ∈ Icc (0:ℝ) 1,
        deriv (deriv path) t = -connection γ (path t) (deriv path t) (deriv path t)

def endpoint (expMap : X n × X n → X n) (r : X n → ℝ) (p : X n × X n) : X n :=
  expMap (p.1, r p.1 • p.2)

def closedBallImage (γ : MetricField n) (expMap : X n × X n → X n) (r : X n → ℝ) (y : X n) : Set (X n) :=
  (fun v => expMap (y,v)) '' disk γ y (r y)

def HarmonicOnBall (g : MetricField n) (ball : Set (X n)) (u : X n → ℝ) : Prop :=
  smoothNear u ball ∧ ∀ x ∈ interior ball, laplace g u x = 0

/-- Solvability for smooth boundary data and uniqueness of the interior restriction. -/
def Dirichlet (Y : Set (X n)) (γ g₁ : MetricField n) (expMap : X n × X n → X n) (r : X n → ℝ) : Prop :=
  ∀ y ∈ Y, ∀ a : X n → ℝ, smoothNear a (sphereAt γ y) →
    let ball := closedBallImage γ expMap r y
    let solves := fun u => HarmonicOnBall g₁ ball u ∧
      ∀ v ∈ sphereAt γ y, u (endpoint expMap r (y,v)) = a v
    ∃ u, solves u ∧ ∀ w, solves w → EqOn u w ball

def standardSphere (n : ℕ) := Metric.sphere (0 : X n) 1

/-- The Haar sphere measure normalized to total mass one in positive dimension. -/
def sphereProbability (n : ℕ) : Measure ↥(standardSphere n) :=
  let μ := (volume : Measure (X n)).toSphere
  (μ univ)⁻¹ • μ

def sphereAverage (e : Frame n) (y : X n) (f : X n → ℂ) : ℂ :=
  ∫ w : ↥(standardSphere n), f (∑ i, (w.val i) • e y i) ∂sphereProbability n

def adjointField (A : TraceAdjoint n) (i : I n) (v : Field n) (p : X n × X n) : ℂ :=
  A i p.1 (fun w => v (p.1,w)) p.2

/-- Duality against every smooth first-metric Dirichlet solution, with the solution held fixed
    while the boundary moves. Real Dirichlet traces determine both parts of a complex field. -/
def IsMovingTraceAdjoint (Y : Set (X n)) (γ g₁ : MetricField n) (e : Frame n)
    (expMap : X n × X n → X n) (r : X n → ℝ) (A : TraceAdjoint n) : Prop :=
  ∀ i (v : Field n), smoothNear v (bundle Y γ) →
    smoothNear (adjointField A i v) (bundle Y γ) ∧
    ∀ y ∈ Y, ∀ u, HarmonicOnBall g₁ (closedBallImage γ expMap r y) u →
      let trace := fun p => u (endpoint expMap r p)
      sphereAverage e y (fun w => adjointField A i v (y,w) * (trace (y,w) : ℝ)) =
        sphereAverage e y (fun w => v (y,w) * (horizontal γ trace y w (axis i) : ℝ))

def traceDerivative (γ : MetricField n) (A : TraceAdjoint n) (j : I n) (φ : Field n)
    (p : X n × X n) : ℂ :=
  horizontal γ φ p.1 p.2 (axis j) + adjointField A j φ p

def movingTrace (γ g₂ : MetricField n) (r : X n → ℝ) (A : TraceAdjoint n)
    (φ : Field n) (p : X n × X n) : ℂ :=
  let W := fun j => traceDerivative γ A j φ
  r p.1 * ((∑ i, ∑ j, (principal γ g₂ p.1 i j : ℂ) *
    (traceDerivative γ A i (W j) p -
      ∑ k, (christoffel γ p.1 k i j : ℂ) * W k p)) +
    ∑ k, (drift γ g₂ p.1 k : ℂ) * W k p)

end CalderonN
