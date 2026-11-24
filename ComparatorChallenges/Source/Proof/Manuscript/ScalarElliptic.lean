module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.ProductMetricHessian
public import Proof.CalderonN.FixedKernelIntegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Proof.CalderonN.Coordinates

@[expose] public section

open Set MeasureTheory
open scoped ContDiff
open CalderonN

noncomputable section

namespace CalderonPaper

/-- A real scalar second-order operator whose principal symbol is the
inverse metric. The first- and zeroth-order coefficients are independent. -/
structure ScalarElliptic (n : ℕ) where
  metric : MetricField n
  first : X n → I n → ℝ
  zeroth : X n → ℝ

namespace ScalarElliptic

variable {n : ℕ}

/-- The principal coefficient is the matrix inverse of the metric. -/
abbrev principalMatrix (L : ScalarElliptic n) (x : X n) : Mat n := (L.metric x)⁻¹

def apply (L : ScalarElliptic n) (u : X n → ℝ) (x : X n) : ℝ :=
  parameterSecondOrder (L.principalMatrix x) (L.first x) (L.zeroth x) u x

def SmoothOn (L : ScalarElliptic n) (D : Set (X n)) : Prop :=
  SmoothMetric D L.metric ∧
  (∀ i, ContDiffOn ℝ ∞ (fun x => L.first x i) D) ∧ ContDiffOn ℝ ∞ L.zeroth D

def SolvesOn (L : ScalarElliptic n) (D : Set (X n)) (u : X n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u D ∧ ∀ x ∈ D, L.apply u x = 0

def ProductSolvesOn (L M : ScalarElliptic n) (U : Set ((X n) × (X n)))
    (F : (X n) × (X n) → ℝ) : Prop :=
  ContDiffOn ℝ ∞ F U ∧
  (∀ z ∈ U, L.apply (fun x => F (x, z.2)) z.1 = 0) ∧
  (∀ z ∈ U, M.apply (fun y => F (z.1, y)) z.2 = 0)

def CoefficientBound (L : ScalarElliptic n) (D : Set (X n))
    (a A : ℝ) (N : ℕ) : Prop :=
  (∀ x ∈ D, ∀ v : X n, a * ‖v‖ ^ 2 ≤
    metricPair L.principalMatrix x v v) ∧
  ∀ x ∈ D, ∀ j ≤ N,
    (∀ i k, ‖iteratedFDeriv ℝ j (fun z => L.principalMatrix z i k) x‖ ≤ A) ∧
    (∀ i, ‖iteratedFDeriv ℝ j (fun z => L.first z i) x‖ ≤ A) ∧
    ‖iteratedFDeriv ℝ j L.zeroth x‖ ≤ A

/-- Coordinate Lebesgue measures on both factors of a cross. -/
def crossMeasure (D S : Set (X n)) : Measure ((X n) × (X n)) :=
  ((volume : Measure (X n)).restrict D).prod ((volume : Measure (X n)).restrict S)

/-- Variable-coefficient interpolation for every square-integrable smooth
solution on the larger domain. The exponent on the observation norm is γ. -/
def Interpolates (L : ScalarElliptic n) (D S O : Set (X n)) (C γ : ℝ) : Prop :=
  ∀ u : X n → ℝ, L.SolvesOn D u → MemLp u 2 ((volume : Measure (X n)).restrict D) →
    lpNorm u 2 ((volume : Measure (X n)).restrict O) ≤
      C * (lpNorm u 2 ((volume : Measure (X n)).restrict S)) ^ γ *
          (lpNorm u 2 ((volume : Measure (X n)).restrict D)) ^ (1 - γ)

end ScalarElliptic
end CalderonPaper

namespace CalderonPaper.ScalarElliptic

open Set MeasureTheory CalderonN

variable {n : ℕ}

def CrossData (L₁ L₂ : ScalarElliptic n) (D₁ D₂ S₁ S₂ : Set (X n))
    (F : (X n) × (X n) → ℝ) (M : ℝ) : Prop :=
  L₁.ProductSolvesOn L₂ (D₁ ×ˢ S₂) F ∧
  L₁.ProductSolvesOn L₂ (S₁ ×ˢ D₂) F ∧
  MemLp F 2 (crossMeasure D₁ S₂) ∧
  MemLp F 2 (crossMeasure S₁ D₂) ∧
  lpNorm F 2 (crossMeasure D₁ S₂) + lpNorm F 2 (crossMeasure S₁ D₂) ≤ M

def CrossExtension (L₁ L₂ : ScalarElliptic n) (S₁ S₂ O₁ O₂ : Set (X n))
    (F G : (X n) × (X n) → ℝ) : Prop :=
  L₁.ProductSolvesOn L₂ (O₁ ×ˢ O₂) G ∧
  EqOn G F (O₁ ×ˢ (O₂ ∩ S₂)) ∧ EqOn G F ((O₁ ∩ S₁) ×ˢ O₂)

end CalderonPaper.ScalarElliptic

namespace CalderonPaper.ScalarElliptic

open Set CalderonN
open scoped ContDiff

variable {n : ℕ}

/-- Smooth parameter dependence in the coordinate patch, including the
lower-order coefficients. This expresses a family of smooth perturbations. -/
def SmoothFamilyOn (L : ℝ → ScalarElliptic n) (D : Set (X n)) : Prop :=
  (∀ a, (L a).SmoothOn D) ∧
  (∀ i j, ContDiffOn ℝ ∞ (fun q : ℝ × (X n) => (L q.1).metric q.2 i j) (univ ×ˢ D)) ∧
  (∀ i, ContDiffOn ℝ ∞ (fun q : ℝ × (X n) => (L q.1).first q.2 i) (univ ×ˢ D)) ∧
  ContDiffOn ℝ ∞ (fun q : ℝ × (X n) => (L q.1).zeroth q.2) (univ ×ˢ D)

end CalderonPaper.ScalarElliptic
