import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators

namespace ShrinkingSpheres

abbrev I := Fin 3
abbrev X := EuclideanSpace ℝ I
abbrev Mat := Matrix I I ℝ
abbrev MetricField := X → Mat
abbrev Field := X × X → ℂ
abbrev Frame := X → I → X
abbrev TraceAdjoint := I → X → (X → ℂ) → X → ℂ

def axis (i : I) : X := EuclideanSpace.single i 1

def metricPair (g : MetricField) (y u v : X) : ℝ :=
  ∑ i, ∑ j, g y i j * u i * v j

def coordDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : I) (f : X → E) (y : X) : E := fderiv ℝ f y (axis i)

def christoffel (g : MetricField) (y : X) (k i j : I) : ℝ :=
  (∑ l, (g y)⁻¹ k l * (coordDeriv i (fun x => g x l j) y +
    coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y)) / 2

def connection (g : MetricField) (y a v : X) : X :=
  WithLp.toLp 2 fun k => ∑ i, ∑ j, christoffel g y k i j * a i * v j

def horizontal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (F : X × X → E) (y v a : X) : E :=
  fderiv ℝ F (y,v) (a, -connection g y a v)

def principal (γ g₂ : MetricField) (y : X) : Mat :=
  (3 / ((γ y) * (g₂ y)⁻¹).trace) • (g₂ y)⁻¹

def drift (γ g₂ : MetricField) (y : X) (k : I) : ℝ :=
  ∑ i, ∑ j, principal γ g₂ y i j * (christoffel γ y k i j - christoffel g₂ y k i j)

def laplace (g : MetricField) (u : X → ℝ) (y : X) : ℝ :=
  ∑ i, ∑ j, (g y)⁻¹ i j * (coordDeriv i (coordDeriv j u) y -
    ∑ k, christoffel g y k i j * coordDeriv k u y)

def covJet (g : MetricField) (f : X → ℝ) : (n : ℕ) → X → (Fin n → I) → ℝ
  | 0, y, _ => f y
  | n+1, y, idx =>
    coordDeriv (idx 0) (fun x => covJet g f n x (Fin.tail idx)) y -
      ∑ t : Fin n, ∑ k, christoffel g y k (idx 0) (idx t.succ) *
        covJet g f n y (Function.update (Fin.tail idx) t k)

def jetNorm (g : MetricField) (e : Frame) (f : X → ℝ) (n : ℕ) (y : X) : ℝ :=
  Real.sqrt (∑ a : Fin n → I,
    (∑ b : Fin n → I, (covJet g f n y b) * ∏ t, e y (a t) (b t)) ^ 2)

def beta (g : MetricField) (r : X → ℝ) (y : X) : ℝ :=
  let f := fun x => Real.log (r x)
  Real.sqrt (∑ i, ∑ j, (g y)⁻¹ i j * coordDeriv i f y * coordDeriv j f y)

def Profile (Y : Set X) (g : MetricField) (e : Frame) (r : X → ℝ)
    (floor c₀ : ℝ) (Cj : Fin 9 → ℝ) : Prop :=
  let f := fun x => Real.log (r x)
  ContDiffOn ℝ ∞ r Y ∧ ∀ y ∈ Y,
    0 < r y ∧ floor ≤ beta g r y ∧
    (∀ v : X, (∑ i, ∑ j, covJet g f 2 y ![i,j] * v i * v j) ≤
      -(c₀ * beta g r y) * metricPair g y v v) ∧
    ∀ j : Fin 9, 1 ≤ j.val → jetNorm g e f j.val y ≤ Cj j * (beta g r y)^j.val

def chartPartial (a b c : ℕ) (f : X → ℝ) : X → ℝ :=
  (coordDeriv 0)^[a] ((coordDeriv 1)^[b] ((coordDeriv 2)^[c] f))

def smallJet (γ g₂ : MetricField) (y : X) : ℝ :=
  ∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range (9-a), ∑ c ∈ Finset.range (9-a-b),
    Real.sqrt (∑ i, ∑ j, (chartPartial a b c (fun x =>
      (principal γ g₂ x - (γ x)⁻¹) i j) y)^2)

def Small (Y : Set X) (γ g₂ : MetricField) (r : X → ℝ) (ε : ℝ) : Prop :=
  ∀ y ∈ Y, smallJet γ g₂ y ≤ ε * r y ∧ r y * (beta γ r y)^2 ≤ ε

def sphereAt (γ : MetricField) (y : X) : Set X := {v | metricPair γ y v v = 1}

def disk (γ : MetricField) (y : X) (s : ℝ) : Set X := {v | metricPair γ y v v ≤ s^2}

def smoothNear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (s : Set E) : Prop :=
  ∃ V, IsOpen V ∧ s ⊆ V ∧ ContDiffOn ℝ ∞ f V

def bundle (Y : Set X) (γ : MetricField) : Set (X × X) :=
  {p | p.1 ∈ Y ∧ p.2 ∈ sphereAt γ p.1}

/-- A smooth system of normal coordinates about every center, specified by its geodesic IVP. -/
def NormalCoordinates (Y Ω : Set X) (γ : MetricField) (expMap : X × X → X)
    (radius : X → ℝ) : Prop :=
  let tube : Set (X × X) := {p | p.1 ∈ Y ∧ p.2 ∈ disk γ p.1 (radius p.1)}
  smoothNear expMap tube ∧ ∀ y ∈ Y,
    0 < radius y ∧
    InjOn (fun v => expMap (y,v)) (disk γ y (radius y)) ∧
    ∀ v ∈ disk γ y (radius y),
      expMap (y,v) ∈ Ω ∧
      Function.Bijective (fderiv ℝ (fun w => expMap (y,w)) v) ∧
      let path := fun t : ℝ => expMap (y,t • v)
      path 0 = y ∧ deriv path 0 = v ∧ ∀ t ∈ Icc (0:ℝ) 1,
        deriv (deriv path) t = -connection γ (path t) (deriv path t) (deriv path t)

def endpoint (expMap : X × X → X) (r : X → ℝ) (p : X × X) : X :=
  expMap (p.1, r p.1 • p.2)

def closedBallImage (γ : MetricField) (expMap : X × X → X) (r : X → ℝ) (y : X) : Set X :=
  (fun v => expMap (y,v)) '' disk γ y (r y)

def HarmonicOnBall (g : MetricField) (ball : Set X) (u : X → ℝ) : Prop :=
  smoothNear u ball ∧ ∀ x ∈ interior ball, laplace g u x = 0

/-- Solvability for smooth boundary data and uniqueness of the interior restriction. -/
def Dirichlet (Y : Set X) (γ g₁ : MetricField) (expMap : X × X → X) (r : X → ℝ) : Prop :=
  ∀ y ∈ Y, ∀ a : X → ℝ, smoothNear a (sphereAt γ y) →
    let ball := closedBallImage γ expMap r y
    let solves := fun u => HarmonicOnBall g₁ ball u ∧
      ∀ v ∈ sphereAt γ y, u (endpoint expMap r (y,v)) = a v
    ∃ u, solves u ∧ ∀ w, solves w → EqOn u w ball

def standardSphere := Metric.sphere (0:X) 1

def sphereAverage (e : Frame) (y : X) (f : X → ℂ) : ℂ :=
  let μ := (volume : Measure X).toSphere
  ∫ w : ↥standardSphere, f (∑ i, (w.val i) • e y i) ∂((μ univ)⁻¹ • μ)

def adjointField (A : TraceAdjoint) (i : I) (v : Field) (p : X × X) : ℂ :=
  A i p.1 (fun w => v (p.1,w)) p.2

/-- Duality against every smooth first-metric Dirichlet solution, with the solution held fixed
    while the boundary moves. Real Dirichlet traces determine both parts of a complex field. -/
def IsMovingTraceAdjoint (Y : Set X) (γ g₁ : MetricField) (e : Frame)
    (expMap : X × X → X) (r : X → ℝ) (A : TraceAdjoint) : Prop :=
  ∀ i (v : Field), smoothNear v (bundle Y γ) →
    smoothNear (adjointField A i v) (bundle Y γ) ∧
    ∀ y ∈ Y, ∀ u, HarmonicOnBall g₁ (closedBallImage γ expMap r y) u →
      let trace := fun p => u (endpoint expMap r p)
      sphereAverage e y (fun w => adjointField A i v (y,w) * (trace (y,w) : ℝ)) =
        sphereAverage e y (fun w => v (y,w) * (horizontal γ trace y w (axis i) : ℝ))

def traceDerivative (γ : MetricField) (A : TraceAdjoint) (j : I) (φ : Field)
    (p : X × X) : ℂ :=
  horizontal γ φ p.1 p.2 (axis j) + adjointField A j φ p

def movingTrace (γ g₂ : MetricField) (r : X → ℝ) (A : TraceAdjoint)
    (φ : Field) (p : X × X) : ℂ :=
  let W := fun j => traceDerivative γ A j φ
  r p.1 * ((∑ i, ∑ j, (principal γ g₂ p.1 i j : ℂ) *
    (traceDerivative γ A i (W j) p -
      ∑ k, (christoffel γ p.1 k i j : ℂ) * W k p)) +
    ∑ k, (drift γ g₂ p.1 k : ℂ) * W k p)

/-- Legendre polynomials with P_k(1)=1. The addition formula on the probability two-sphere
    gives the kernel (2k+1) P_k for projection to harmonic degree k. -/
def legendre (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => t
  | k+2 => ((2*(k:ℝ)+3)*t*legendre t (k+1) - ((k:ℝ)+1)*legendre t k) / ((k:ℝ)+2)

def degreePart (γ : MetricField) (e : Frame) (k : ℕ) (y : X) (u : X → ℂ) (w : X) : ℂ :=
  ((2*(k:ℝ)+1) : ℝ) * sphereAverage e y (fun z => (legendre (metricPair γ y w z) k : ℂ) * u z)

def fiberSq (e : Frame) (y : X) (u : X → ℂ) : ℝ :=
  (sphereAverage e y (fun w => ((‖u w‖^2 : ℝ) : ℂ))).re

def sobolevSq (γ : MetricField) (e : Frame) (s : ℝ) (y : X) (u : X → ℂ) : ℝ :=
  ∑' k : ℕ, (1+(k:ℝ))^(2*s) * fiberSq e y (degreePart γ e k y u)

def energySq (Y : Set X) (γ : MetricField) (e : Frame) (r : X → ℝ) (φ : Field) : ℝ :=
  ∫ y in Y, Real.sqrt (γ y).det *
    (let b := beta γ r y
     let u := fun w => φ (y,w)
     let H := fun i w => horizontal γ φ y w (e y i)
     (∑ i, fiberSq e y (H i)) + b^2 * sobolevSq γ e 1 y u +
       b⁻¹ * (∑ i, sobolevSq γ e (1/2) y (H i)) + b * sobolevSq γ e (3/2) y u)

def outputSq (Y : Set X) (γ : MetricField) (e : Frame) (V : Field) : ℝ :=
  ∫ y in Y, Real.sqrt (γ y).det * fiberSq e y (fun w => V (y,w))

def Test (Y : Set X) (γ : MetricField) (e : Frame) (φ : Field) : Prop :=
  smoothNear φ (bundle Y γ) ∧
  (∃ K, IsCompact K ∧ K ⊆ Y ∧ ∀ y ∈ Y \ K, ∀ w ∈ sphereAt γ y, φ (y,w) = 0) ∧
  ∀ y ∈ Y, sphereAverage e y (fun w => φ (y,w)) = 0

def Elliptic (Ω : Set X) (K : ℝ) (g : MetricField) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) Ω) ∧
  ∀ y ∈ Ω, (g y).transpose = g y ∧ ∀ v : X,
    K⁻¹ * ‖v‖^2 ≤ metricPair g y v v ∧ metricPair g y v v ≤ K * ‖v‖^2

/-- The smooth background budgets concern the reference and first metric. The full second
    metric enters through ellipticity, bounded drift, and its normalized tensor in Small. -/
def Background (Ω : Set X) (K : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ) (γ g₁ g₂ : MetricField) (e : Frame) : Prop :=
  Elliptic Ω K γ ∧ Elliptic Ω K g₁ ∧ Elliptic Ω K g₂ ∧
  (∀ y ∈ Ω, ∃ a : ℝ, 0 < a ∧ γ y = a • g₁ y) ∧
  (∀ g ∈ ({γ, g₁} : Set MetricField), ∀ (j : Fin (m+1)) i l, ∀ y ∈ Ω,
    ‖iteratedFDeriv ℝ j.val (fun x => g x i l) y‖ ≤ M j) ∧
  (∀ y ∈ Ω, ∀ i, |drift γ g₂ y i| ≤ K) ∧
  (∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Ω) ∧
  ∀ y ∈ Ω, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0

/-- One configuration. The exponential map and adjoint describe the physical fields in the
    same coordinates as the two metrics and the chosen orthonormal frame. -/
structure Data where
  γ : MetricField
  g₁ : MetricField
  g₂ : MetricField
  frame : Frame
  radius : X → ℝ
  expMap : X × X → X
  adjoint : TraceAdjoint

def Admissible (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ)
    (Cj : Fin 9 → ℝ) (floor ε : ℝ) (d : Data) : Prop :=
  Background Ω K M d.γ d.g₁ d.g₂ d.frame ∧
  NormalCoordinates Y Ω d.γ d.expMap (fun y => max ρ (d.radius y)) ∧
  Dirichlet Y d.γ d.g₁ d.expMap d.radius ∧
  IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius d.adjoint ∧
  Profile Y d.γ d.frame d.radius floor c₀ Cj ∧ Small Y d.γ d.g₂ d.radius ε

def energyNorm (Y : Set X) (d : Data) (φ : Field) : ℝ :=
  Real.sqrt (energySq Y d.γ d.frame d.radius φ)

def traceNorm (Y : Set X) (d : Data) (φ : Field) : ℝ :=
  Real.sqrt (outputSq Y d.γ d.frame (movingTrace d.γ d.g₂ d.radius d.adjoint φ))

def UniformEstimate (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ)
    (Cj : Fin 9 → ℝ) (floor ε₀ C : ℝ) : Prop :=
  ∀ d ε, 0 ≤ ε → ε ≤ ε₀ → Admissible Y Ω K ρ c₀ M Cj floor ε d →
    ∀ φ, Test Y d.γ d.frame φ → energyNorm Y d φ ≤ C * traceNorm Y d φ

/-- Proposition 5.3, TeX label angular:coercivity. A finite background budget and common
    constants suffice for every admissible metric, radius and smooth test. -/
theorem coercivity (Y Ω : Set X) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hcpt : IsCompact (closure Y)) (hin : closure Y ⊆ Ω) :
    ∃ m : ℕ, ∀ (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ),
      1 ≤ K → 0 < ρ → 0 < c₀ → ∃ floor ε₀ C : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
        UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C := by
  sorry

end ShrinkingSpheres
