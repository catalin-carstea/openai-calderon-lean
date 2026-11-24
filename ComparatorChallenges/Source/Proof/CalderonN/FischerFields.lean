module

public import Proof.CalderonN.MetricConnection
public import Proof.Archive.AngularCoefficient
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Proof.CalderonN.Coordinates

@[expose] public section

/- Port of FischerFields.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finitePolynomialField (b : ι → MvPolynomial (Fin n) ℝ)
    (c : (X n) → ι → ℝ) (x : (X n)) : MvPolynomial (Fin n) ℝ := ∑ i, c x i • b i

end CalderonN
