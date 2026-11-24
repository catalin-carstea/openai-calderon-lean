module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace

/- Port of the coordinate operators from the checked 3D Theorem 3.1 packet
   (55d37bfe), Proof/LocalMetricExtension/Coercivity.lean, and its Proposition 5.3 source. -/

@[expose] public section

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace CalderonN

variable {n : ℕ}

abbrev I (n : ℕ) := Fin n
abbrev X (n : ℕ) := EuclideanSpace ℝ (I n)
abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℝ
abbrev MetricField (n : ℕ) := X n → Mat n
abbrev Field (n : ℕ) := X n × X n → ℂ
abbrev Frame (n : ℕ) := X n → I n → X n
abbrev TraceAdjoint (n : ℕ) := I n → X n → (X n → ℂ) → X n → ℂ

def axis (i : I n) : X n := EuclideanSpace.single i 1

def metricPair (g : MetricField n) (y u v : X n) : ℝ :=
  ∑ i, ∑ j, g y i j * u i * v j

def coordDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : I n) (f : X n → E) (y : X n) : E := fderiv ℝ f y (axis i)

def christoffel (g : MetricField n) (y : X n) (k i j : I n) : ℝ :=
  (∑ l, (g y)⁻¹ k l * (coordDeriv i (fun x => g x l j) y +
    coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y)) / 2

def connection (g : MetricField n) (y a v : X n) : X n :=
  WithLp.toLp 2 fun k => ∑ i, ∑ j, christoffel g y k i j * a i * v j

def horizontal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField n) (F : X n × X n → E) (y v a : X n) : E :=
  fderiv ℝ F (y,v) (a, -connection g y a v)

def principal (γ g₂ : MetricField n) (y : X n) : Mat n :=
  ((n : ℝ) / ((γ y) * (g₂ y)⁻¹).trace) • (g₂ y)⁻¹

def drift (γ g₂ : MetricField n) (y : X n) (k : I n) : ℝ :=
  ∑ i, ∑ j, principal γ g₂ y i j * (christoffel γ y k i j - christoffel g₂ y k i j)

def laplace (g : MetricField n) (u : X n → ℝ) (y : X n) : ℝ :=
  ∑ i, ∑ j, (g y)⁻¹ i j * (coordDeriv i (coordDeriv j u) y -
    ∑ k, christoffel g y k i j * coordDeriv k u y)

def covJet (g : MetricField n) (f : X n → ℝ) : (j : ℕ) → X n → (Fin j → I n) → ℝ
  | 0, y, _ => f y
  | j+1, y, idx =>
    coordDeriv (idx 0) (fun x => covJet g f j x (Fin.tail idx)) y -
      ∑ t : Fin j, ∑ k, christoffel g y k (idx 0) (idx t.succ) *
        covJet g f j y (Function.update (Fin.tail idx) t k)

def jetNorm (g : MetricField n) (e : Frame n) (f : X n → ℝ) (j : ℕ) (y : X n) : ℝ :=
  Real.sqrt (∑ a : Fin j → I n,
    (∑ b : Fin j → I n, (covJet g f j y b) * ∏ t, e y (a t) (b t)) ^ 2)

def beta (g : MetricField n) (r : X n → ℝ) (y : X n) : ℝ :=
  let f := fun x => Real.log (r x)
  Real.sqrt (∑ i, ∑ j, (g y)⁻¹ i j * coordDeriv i f y * coordDeriv j f y)

def Profile (Y : Set (X n)) (g : MetricField n) (e : Frame n) (r : X n → ℝ)
    (floor c₀ : ℝ) (Cj : Fin 9 → ℝ) : Prop :=
  let f := fun x => Real.log (r x)
  ContDiffOn ℝ ∞ r Y ∧ ∀ y ∈ Y,
    0 < r y ∧ floor ≤ beta g r y ∧
    (∀ v : X n, (∑ i, ∑ j, covJet g f 2 y ![i,j] * v i * v j) ≤
      -(c₀ * beta g r y) * metricPair g y v v) ∧
    ∀ j : Fin 9, 1 ≤ j.val → jetNorm g e f j.val y ≤ Cj j * (beta g r y)^j.val

/-- Coordinate mixed partial, ordered by increasing coordinate index. -/
def chartPartial (a : I n → ℕ) (f : X n → ℝ) : X n → ℝ :=
  (List.ofFn fun i : I n => (coordDeriv i)^[a i]).foldr (fun D u => D u) f

/-- All multi-indices of total order at most eight, each counted once. -/
def smallJet (γ g₂ : MetricField n) (y : X n) : ℝ :=
  ∑ a ∈ (Finset.univ : Finset (I n → Fin 9)).filter (fun a => (∑ i, (a i).val) ≤ 8),
    Real.sqrt (∑ i, ∑ j, (chartPartial (fun t => (a t).val) (fun x =>
      (principal γ g₂ x - (γ x)⁻¹) i j) y)^2)

def Small (Y : Set (X n)) (γ g₂ : MetricField n) (r : X n → ℝ) (ε : ℝ) : Prop :=
  ∀ y ∈ Y, smallJet γ g₂ y ≤ ε * r y ∧ r y * (beta γ r y)^2 ≤ ε

end CalderonN
