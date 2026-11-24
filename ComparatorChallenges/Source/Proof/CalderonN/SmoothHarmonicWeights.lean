module

public import Proof.CalderonN.SmoothAmbientAngularCasimir
public import Proof.CalderonN.HarmonicMultiplier
public import Proof.CalderonN.ZonalProjection
public import Proof.CalderonN.SphereFrame
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
public import Proof.CalderonN.SmoothSphereRotation
public import Proof.CalderonN.SphereHarmonicBridge
public import Proof.Archive.FischerPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Proof.CalderonN.HarmonicHilbertDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.SmoothSphereFields

public section

/- Adapted from the smooth Bessel fields in Proposition 5.3 release f308cb9d.
   The weight denominator uses the actual dimension-n Casimir. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields

variable {n : ℕ} [NeZero n]

@[expose] def besselWeight (s : ℝ) (k : ℕ) : ℝ := (1 + (k : ℝ)) ^ s

@[expose] def casimirWeight (n k : ℕ) : ℝ := 1 + (k : ℝ) * ((k : ℝ) + n - 2)

private theorem besselCasimirRatio_bound (hn : 3 ≤ n) (s : ℝ) (hs : s ≤ 2) (k : ℕ) :
    |besselWeight s k / casimirWeight n k| ≤ 2 := sorry

/-- A single shifted Casimir derivative controls every Bessel lift of order at most two. -/
def ambientBesselField (hn : 3 ≤ n) (s : ℝ) (hs : s ≤ 2)
    (G : X n × X n → ℝ) (hG : ContDiff ℝ ∞ G) (y : X n) : SphereL2 n :=
  harmonicMultiplier (fun k => besselWeight s k / casimirWeight n k) 2
    (by norm_num) (besselCasimirRatio_bound hn s hs)
    (ambientSphereL2 (ambientShiftedAngularCasimir G) (contDiff_ambientShiftedAngularCasimir G hG) y)

end CalderonN
