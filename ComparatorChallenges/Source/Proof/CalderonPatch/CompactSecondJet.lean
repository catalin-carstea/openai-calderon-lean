module

public import Proof.CalderonPatch.HarmonicJets
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.LinearAlgebra.Isomorphisms
public import Proof.CalderonN.Coordinates
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LSum
public import Proof.CalderonN.ChartSchwarzWords
import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Proof.CalderonN.Hessian
import Proof.CalderonN.Chart
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

noncomputable section
open Filter Matrix Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace CalderonPatch

open CalderonN (I X Mat axis coordDeriv hessian chartDerivativeWord)

variable {n : ℕ} [NeZero n]

/-- A scalar second jet in a chosen open chart. -/
def smoothSecondJet {U : Set (X n)} (hU : IsOpen U) {x : X n} (hx : x ∈ U)
    (f : X n → ℝ) (hf : ContDiffOn ℝ ∞ f U) : ScalarSecondJet n :=
  secondJet f x (CalderonN.hessian_transpose hU hf hx)

end CalderonPatch
