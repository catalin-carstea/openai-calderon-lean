module

public import Proof.CalderonN.SphereHarmonicBridge
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Gamma

@[expose] public section

/- Port of the Gaussian radial comparison and sphere pairing from Proposition 5.3
   check f308cb9d, Archive/Literature{GaussianSphere,SphereIntegrals,SphereFischerInner}. -/
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace ENNReal

namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

variable {n : ℕ}



variable [NeZero n]







theorem sphereFischerInner (n : ℕ) [NeZero n] : SphereFischerInner n := sorry

end OAI.AnisotropicCalderon.SphereHarmonic
