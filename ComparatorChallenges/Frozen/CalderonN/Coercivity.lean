module

public import ComparatorChallenges.Frozen.CalderonN.MovingTrace

/- Port of the norms and estimate from the checked 3D Theorem 3.1 packet
   (55d37bfe), Proof/LocalMetricExtension/Coercivity.lean, and its Proposition 5.3 source. -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators

namespace CalderonN

variable {n : ℕ}

/-- Normalized zonal polynomial on the unit sphere in dimension n.
The recurrence is the normalized Gegenbauer recurrence for n ≥ 3. -/
def zonal (n : ℕ) (t : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => t
  | k+2 => ((2*(k:ℝ)+n)*t*zonal n t (k+1) - ((k:ℝ)+1)*zonal n t k) /
      ((k:ℝ)+(n:ℝ)-1)

/-- Dimension of homogeneous harmonic polynomials of the given degree. -/
def harmonicMultiplicity (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => n
  | k+2 => (Nat.choose (n + k + 1) (k + 2)) - (Nat.choose (n + k - 1) k)

def degreePart (γ : MetricField n) (e : Frame n) (k : ℕ) (y : X n)
    (u : X n → ℂ) (w : X n) : ℂ :=
  (harmonicMultiplicity n k : ℂ) *
    sphereAverage e y (fun z => (zonal n (metricPair γ y w z) k : ℂ) * u z)

def fiberSq (e : Frame n) (y : X n) (u : X n → ℂ) : ℝ :=
  (sphereAverage e y (fun w => ((‖u w‖^2 : ℝ) : ℂ))).re

def sobolevSq (γ : MetricField n) (e : Frame n) (s : ℝ) (y : X n) (u : X n → ℂ) : ℝ :=
  ∑' k : ℕ, (1+(k:ℝ))^(2*s) * fiberSq e y (degreePart γ e k y u)

def energySq (Y : Set (X n)) (γ : MetricField n) (e : Frame n) (r : X n → ℝ) (φ : Field n) : ℝ :=
  ∫ y in Y, Real.sqrt (γ y).det *
    (let b := beta γ r y
     let u := fun w => φ (y,w)
     let H := fun i w => horizontal γ φ y w (e y i)
     (∑ i, fiberSq e y (H i)) + b^2 * sobolevSq γ e 1 y u +
       b⁻¹ * (∑ i, sobolevSq γ e (1/2) y (H i)) + b * sobolevSq γ e (3/2) y u)

def outputSq (Y : Set (X n)) (γ : MetricField n) (e : Frame n) (V : Field n) : ℝ :=
  ∫ y in Y, Real.sqrt (γ y).det * fiberSq e y (fun w => V (y,w))

def Test (Y : Set (X n)) (γ : MetricField n) (e : Frame n) (φ : Field n) : Prop :=
  smoothNear φ (bundle Y γ) ∧
  (∃ K, IsCompact K ∧ K ⊆ Y ∧ ∀ y ∈ Y \ K, ∀ w ∈ sphereAt γ y, φ (y,w) = 0) ∧
  ∀ y ∈ Y, sphereAverage e y (fun w => φ (y,w)) = 0

def Elliptic (Ω : Set (X n)) (K : ℝ) (g : MetricField n) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) Ω) ∧
  ∀ y ∈ Ω, (g y).transpose = g y ∧ ∀ v : X n,
    K⁻¹ * ‖v‖^2 ≤ metricPair g y v v ∧ metricPair g y v v ≤ K * ‖v‖^2

/-- The smooth background budgets concern the reference and first metric. The full second
    metric enters through ellipticity, bounded drift, and its normalized tensor in Small. -/
def Background (Ω : Set (X n)) (K : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ) (γ g₁ g₂ : MetricField n) (e : Frame n) : Prop :=
  Elliptic Ω K γ ∧ Elliptic Ω K g₁ ∧ Elliptic Ω K g₂ ∧
  (∀ y ∈ Ω, ∃ a : ℝ, 0 < a ∧ γ y = a • g₁ y) ∧
  (∀ g ∈ ({γ, g₁} : Set (MetricField n)), ∀ (j : Fin (m+1)) i l, ∀ y ∈ Ω,
    ‖iteratedFDeriv ℝ j.val (fun x => g x i l) y‖ ≤ M j) ∧
  (∀ y ∈ Ω, ∀ i, |drift γ g₂ y i| ≤ K) ∧
  (∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Ω) ∧
  ∀ y ∈ Ω, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0

/-- One configuration. The exponential map and adjoint describe the physical fields in the
    same coordinates as the two metrics and the chosen orthonormal frame. -/
structure Data (n : ℕ) where
  γ : MetricField n
  g₁ : MetricField n
  g₂ : MetricField n
  frame : Frame n
  radius : X n → ℝ
  expMap : X n × X n → X n
  adjoint : TraceAdjoint n

def Admissible (Y Ω : Set (X n)) (K ρ c₀ : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ)
    (Cj : Fin 9 → ℝ) (floor ε : ℝ) (d : Data n) : Prop :=
  Background Ω K M d.γ d.g₁ d.g₂ d.frame ∧
  NormalCoordinates Y Ω d.γ d.expMap (fun y => max ρ (d.radius y)) ∧
  Dirichlet Y d.γ d.g₁ d.expMap d.radius ∧
  IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius d.adjoint ∧
  Profile Y d.γ d.frame d.radius floor c₀ Cj ∧ Small Y d.γ d.g₂ d.radius ε

def energyNorm (Y : Set (X n)) (d : Data n) (φ : Field n) : ℝ :=
  Real.sqrt (energySq Y d.γ d.frame d.radius φ)

def traceNorm (Y : Set (X n)) (d : Data n) (φ : Field n) : ℝ :=
  Real.sqrt (outputSq Y d.γ d.frame (movingTrace d.γ d.g₂ d.radius d.adjoint φ))

def UniformEstimate (Y Ω : Set (X n)) (K ρ c₀ : ℝ) {m : ℕ} (M : Fin (m+1) → ℝ)
    (Cj : Fin 9 → ℝ) (floor ε₀ C : ℝ) : Prop :=
  ∀ d ε, 0 ≤ ε → ε ≤ ε₀ → Admissible Y Ω K ρ c₀ M Cj floor ε d →
    ∀ φ, Test Y d.γ d.frame φ → energyNorm Y d φ ≤ C * traceNorm Y d φ

/-- Uniform coercivity of Proposition 5.3 in ambient dimension n. -/
def Coercivity (n : ℕ) : Prop :=
  ∀ (Y Ω : Set (X n)), IsOpen Y → IsOpen Ω → IsCompact (closure Y) → closure Y ⊆ Ω →
    ∃ m : ℕ, ∀ (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ),
      1 ≤ K → 0 < ρ → 0 < c₀ → ∃ floor ε₀ C : ℝ, 1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
        UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C

end CalderonN
