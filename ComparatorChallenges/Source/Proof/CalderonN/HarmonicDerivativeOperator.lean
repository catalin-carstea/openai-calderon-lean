module

public import Proof.CalderonN.SphereDerivativeAdjoint
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.SmoothSphereRotationProjection
public import Proof.CalderonN.SphereHarmonicBridge
public import Proof.CalderonN.ZonalProjection

@[expose] public section

noncomputable section
open MvPolynomial
open scoped InnerProductSpace

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial

variable {n : ℕ} [NeZero n]

def harmonicPolynomialDerivativeMap (m : ℕ) (i : Fin n) :
    harmonicHomogeneous n (m+1) →ₗ[ℝ] harmonicSphereSubspace n m where
  toFun p := ⟨polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin n) ℝ)),
    polynomialSphereL2_mem m _ (pderiv_harmonicHomogeneous_succ m i p p.property)⟩
  map_add' p q := by
    apply Subtype.ext
    change polynomialSphereL2 (pderiv i ((p : MvPolynomial (Fin n) ℝ)+q)) = _
    rw [map_add,map_add]
    rfl
  map_smul' c p := by
    apply Subtype.ext
    change polynomialSphereL2 (pderiv i (c • (p : MvPolynomial (Fin n) ℝ))) =
      c • polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin n) ℝ))
    rw [smul_eq_C_mul,pderiv_C_mul,← smul_eq_C_mul,map_smul]

lemma harmonicPolynomialSphereMap_ker_le_derivative (hF : SphereFischerInner n)
    (m : ℕ) (i : Fin n) :
    LinearMap.ker (harmonicPolynomialSphereMap (m+1)) ≤
      LinearMap.ker (harmonicPolynomialDerivativeMap m i) := sorry

def harmonicDerivativeLinear (hF : SphereFischerInner n) (m : ℕ) (i : Fin n) :
    harmonicSphereSubspace n (m+1) →ₗ[ℝ] harmonicSphereSubspace n m :=
  (harmonicPolynomialSphereMap (m+1)).liftOfSurjective
    (harmonicPolynomialSphereMap_surjective (m+1))
    ⟨harmonicPolynomialDerivativeMap m i,harmonicPolynomialSphereMap_ker_le_derivative hF m i⟩


def harmonicDerivative (hF : SphereFischerInner n) (m : ℕ) (i : Fin n) :
    harmonicSphereSubspace n (m+1) →L[ℝ] harmonicSphereSubspace n m := by
  exact (harmonicDerivativeLinear hF m i).toContinuousLinearMap



end CalderonN
