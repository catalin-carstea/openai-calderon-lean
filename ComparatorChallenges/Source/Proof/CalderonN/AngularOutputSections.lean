module

public import Proof.CalderonN.BoundedHarmonicShift
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.HarmonicMultiplier
public import Proof.CalderonN.SmoothAmbientAngularCasimir
public import Proof.CalderonN.SmoothHarmonicWeights
public import Proof.CalderonN.SmoothSphereFields
public import Proof.CalderonN.SphereHarmonicBridge

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields

variable {n : ℕ} [NeZero n]

private theorem degreeBesselRatio_le (hn : 3 ≤ n) (k : ℕ) :
    |((k : ℝ)+1) * k / casimirWeight n k| ≤ 1 := sorry

/-- The degree operator followed by one Bessel weight on a smooth sphere field. -/
private def ambientDegreeBessel (hn : 3 ≤ n) (G : X n × X n → ℝ)
    (hG : ContDiff ℝ ∞ G) (y : X n) : SphereL2 n :=
  harmonicMultiplier (fun k => ((k : ℝ)+1) * k / casimirWeight n k) 1
    (by norm_num) (degreeBesselRatio_le hn)
    (ambientSphereL2 (ambientShiftedAngularCasimir G) (contDiff_ambientShiftedAngularCasimir G hG) y)

private def weightedAngularBesselSection (hn : 3 ≤ n)
    (H G : X n × X n → ℝ) (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G)
    (b : X n → ℝ) (sign : ℝ) (y : X n) : SphereL2 n :=
  sign • ambientBesselField hn 1 (by norm_num) H hH y + b y • ambientDegreeBessel hn G hG y

variable (hn : 3 ≤ n)
variable (H : I n → X n × X n → ℝ) (G : X n × X n → ℝ)
variable (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G)
variable (b : I n → X n → ℝ)

def angularRaisingSum (y : X n) : SphereL2 n :=
  ∑ i, normalizedRaising i (weightedAngularBesselSection hn (H i) G (hH i) hG (b i) 1 y)

def angularLoweringSum (y : X n) : SphereL2 n :=
  ∑ i, normalizedLowering i (weightedAngularBesselSection hn (H i) G (hH i) hG (b i) (-1) y)

end CalderonN
