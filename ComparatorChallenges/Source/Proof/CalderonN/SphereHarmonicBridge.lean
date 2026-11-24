module

public import Proof.Archive.AngularCoefficient
public import Proof.CalderonN.Coercivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic
public import Proof.Archive.AngularPolynomial
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.MovingTrace

@[expose] public section

/- Port of Proof/Archive/SphereHarmonicBridge.lean from Proposition 5.3 check f308cb9d. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial CalderonN

variable {n : ℕ}

abbrev UnitSphere (n : ℕ) := ↥(Metric.sphere (0 : X n) 1)

/-- The protected probability measure viewed on the canonical metric sphere. -/
abbrev unitSphereProbability (n : ℕ) : Measure (UnitSphere n) := sphereProbability n

abbrev SphereL2 (n : ℕ) := Lp ℝ 2 (unitSphereProbability n)

instance (n : ℕ) : CompactSpace (UnitSphere n) := sorry

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (unitSphereProbability n) := sorry

def polynomialSphere (p : MvPolynomial (Fin n) ℝ) : C(UnitSphere n, ℝ) :=
  ⟨fun x => p.eval (x.val : Fin n → ℝ),
    p.continuous_eval.comp (by fun_prop)⟩

def polynomialSphereLinear : MvPolynomial (Fin n) ℝ →ₗ[ℝ] C(UnitSphere n, ℝ) where
  toFun := polynomialSphere
  map_add' p q := by ext x; simp [polynomialSphere]
  map_smul' c p := by ext x; simp [polynomialSphere]

variable [NeZero n]

def polynomialSphereL2 : MvPolynomial (Fin n) ℝ →ₗ[ℝ] SphereL2 n :=
  (ContinuousMap.toLp 2 (unitSphereProbability n) ℝ).toLinearMap.comp
    polynomialSphereLinear

theorem harmonicHomogeneous_smul_mem (n k : ℕ) (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    p ∈ {q | q.IsHomogeneous k ∧ laplacian q = 0} →
      c • p ∈ {q | q.IsHomogeneous k ∧ laplacian q = 0} := sorry

theorem harmonicHomogeneous_add_mem (n k : ℕ) {a b : MvPolynomial (Fin n) ℝ} :
    a ∈ {q | q.IsHomogeneous k ∧ laplacian q = 0} →
      b ∈ {q | q.IsHomogeneous k ∧ laplacian q = 0} →
        (a + b).IsHomogeneous k ∧ laplacian (a + b) = 0 := sorry

theorem harmonicHomogeneous_zero_mem (n k : ℕ) :
    (0 : MvPolynomial (Fin n) ℝ).IsHomogeneous k ∧
      laplacian (0 : MvPolynomial (Fin n) ℝ) = 0 := sorry

def harmonicHomogeneous (n k : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) where
  carrier := {p | p.IsHomogeneous k ∧ laplacian p = 0}
  add_mem' := @harmonicHomogeneous_add_mem n k
  zero_mem' := harmonicHomogeneous_zero_mem n k
  smul_mem' c p hp := harmonicHomogeneous_smul_mem n k c p hp

def harmonicSphereSubspace (n : ℕ) [NeZero n] (k : ℕ) : Submodule ℝ (SphereL2 n) :=
  (harmonicHomogeneous n k).map polynomialSphereL2

def SphereFischerInner (n : ℕ) [NeZero n] : Prop := ∀ k : ℕ, ∀ p q : MvPolynomial (Fin n) ℝ,
  p ∈ harmonicHomogeneous n k → q ∈ harmonicHomogeneous n k →
    ⟪polynomialSphereL2 p, polynomialSphereL2 q⟫_ℝ = normalizedFischerInner k p q

lemma polynomialSphereL2_mem (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ harmonicHomogeneous n k) :
    polynomialSphereL2 p ∈ harmonicSphereSubspace n k := sorry

end OAI.AnisotropicCalderon.SphereHarmonic
