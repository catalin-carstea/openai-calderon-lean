module

public import ComparatorChallenges.Frozen.CalderonN.Coordinates
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/- Port of Proof/LocalMetricExtension/Chart.lean from the checked 3D Theorem 3.1 packet (55d37bfe). -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff BigOperators

namespace CalderonN

variable {n : ℕ}

def SmoothMetric (Ω : Set (X n)) (g : MetricField n) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) Ω) ∧
    ∀ x ∈ Ω, (g x).PosDef

def Harmonic (Ω : Set (X n)) (g : MetricField n) (u : X n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u Ω ∧ ∀ x ∈ Ω, laplace g u x = 0

def HarmonicCoordinates (Ω : Set (X n)) (g : MetricField n) : Prop :=
  ∀ i : I n, Harmonic Ω g (fun x => x i)

def OffDiagonal (Ω : Set (X n)) : Set (X n × X n) :=
  {p | p.1 ∈ Ω ∧ p.2 ∈ Ω ∧ p.1 ≠ p.2}

/-- The chart-local properties of a Dirichlet Green kernel. The weak law
uses the sign of the inverse of `-Δ_g` and the Riemannian volume density. -/
def GreenGerm (Ω : Set (X n)) (g : MetricField n) (G : X n × X n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ G (OffDiagonal Ω) ∧
    (∀ p ∈ OffDiagonal Ω, G p = G (p.2, p.1)) ∧
    ∀ y ∈ Ω, LocallyIntegrableOn (fun x => G (x, y)) Ω ∧
      ∀ u : X n → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u → tsupport u ⊆ Ω →
        (∫ x in Ω, G (x, y) * (-laplace g u x) * Real.sqrt (g x).det) = u y

/-- A local side of a smooth hypersurface through the origin. The defining
function has nonzero derivative at the origin and the known side is negative. -/
def ContainsSmoothSide (Ω W : Set (X n)) : Prop :=
  ∃ (V : Set (X n)) (s : X n → ℝ), IsOpen V ∧ (0 : X n) ∈ V ∧ V ⊆ Ω ∧
    ContDiffOn ℝ ∞ s V ∧ s 0 = 0 ∧ fderiv ℝ s 0 ≠ 0 ∧
    {x ∈ V | s x < 0} ⊆ W

def hessian (u : X n → ℝ) (x : X n) : Mat n :=
  fun i j => coordDeriv i (coordDeriv j u) x

/-- The first-side coordinate Hessians span the whole symmetric
hyperplane of zero trace against the inverse metric at the origin. -/
def HessianSpanning {m : ℕ} (g : MetricField n) (u : Fin m → X n → ℝ) : Prop :=
  ∀ H : Mat n, H ∈ Submodule.span ℝ (range fun a => hessian (u a) 0) ↔
    H.transpose = H ∧ ((g 0)⁻¹ * H).trace = 0

end CalderonN
