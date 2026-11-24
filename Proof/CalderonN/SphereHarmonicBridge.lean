module

public import Proof.Archive.AngularCoefficient
public import Proof.CalderonN.Moments
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.MvPolynomial

import Mathlib.Tactic

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

instance (n : ℕ) : CompactSpace (UnitSphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X n) 1)

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (unitSphereProbability n) :=
  inferInstanceAs (IsProbabilityMeasure (sphereProbability n))

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

lemma polynomialSphereL2_inner (p q : MvPolynomial (Fin n) ℝ) :
    ⟪polynomialSphereL2 p, polynomialSphereL2 q⟫_ℝ =
      ∫ x : UnitSphere n, p.eval (x.val : Fin n → ℝ) *
        q.eval (x.val : Fin n → ℝ) ∂unitSphereProbability n := by
  change ⟪(ContinuousMap.toLp 2 (unitSphereProbability n) ℝ)
    (polynomialSphere p), (ContinuousMap.toLp 2 (unitSphereProbability n) ℝ)
      (polynomialSphere q)⟫_ℝ = _
  simpa only [ContinuousMap.coe_mk, polynomialSphere,
    starRingEnd_apply, star_trivial, mul_comm] using
    ContinuousMap.inner_toLp (unitSphereProbability n)
      (polynomialSphere p) (polynomialSphere q)

theorem harmonicHomogeneous_smul_mem (n k : ℕ) (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    p ∈ {q | q.IsHomogeneous k ∧ laplacian q = 0} →
      c • p ∈ {q | q.IsHomogeneous k ∧ laplacian q = 0} := by
  intro hp
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_C_mul] using hp.1.C_mul c
  · simpa only [smul_eq_C_mul] using (laplacian_C_mul c p).trans (by rw [hp.2, mul_zero])

theorem harmonicHomogeneous_add_mem (n k : ℕ) {a b : MvPolynomial (Fin n) ℝ} :
    a ∈ {q | q.IsHomogeneous k ∧ laplacian q = 0} →
      b ∈ {q | q.IsHomogeneous k ∧ laplacian q = 0} →
        (a + b).IsHomogeneous k ∧ laplacian (a + b) = 0 := by
  intro hp hq
  refine ⟨hp.1.add hq.1, ?_⟩
  simp only [laplacian, map_add, Finset.sum_add_distrib]
  change laplacian _ + laplacian _ = 0
  rw [hp.2, hq.2, zero_add]

theorem harmonicHomogeneous_zero_mem (n k : ℕ) :
    (0 : MvPolynomial (Fin n) ℝ).IsHomogeneous k ∧
      laplacian (0 : MvPolynomial (Fin n) ℝ) = 0 := ⟨(MvPolynomial.homogeneousSubmodule (Fin n) ℝ k).zero_mem, by simp [laplacian]⟩

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

def OrthogonalSphereHarmonics (n : ℕ) [NeZero n] : Prop := ∀ k m : ℕ, k ≠ m →
  ∀ u ∈ harmonicSphereSubspace n k, ∀ v ∈ harmonicSphereSubspace n m, ⟪u, v⟫_ℝ = 0

def DenseSphereHarmonics (n : ℕ) [NeZero n] : Prop :=
  (⨆ k : ℕ, harmonicSphereSubspace n k).topologicalClosure = ⊤

lemma polynomialSphereL2_norm_sq (hF : SphereFischerInner n) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ∈ harmonicHomogeneous n k) :
    ‖polynomialSphereL2 p‖ ^ 2 = normalizedFischerSquare k p := by
  rw [← real_inner_self_eq_norm_sq, hF k p p hp hp]
  rfl

lemma polynomialSphereL2_eq_zero_iff (hF : SphereFischerInner n) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ∈ harmonicHomogeneous n k) :
    polynomialSphereL2 p = 0 ↔ p = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff, polynomialSphereL2_norm_sq hF k p hp]
  exact normalizedFischerSquare_eq_zero_iff k p

lemma polynomialSphereL2_injective_degree (hF : SphereFischerInner n) (k : ℕ)
    (p q : MvPolynomial (Fin n) ℝ) (hp : p ∈ harmonicHomogeneous n k)
    (hq : q ∈ harmonicHomogeneous n k) :
    polynomialSphereL2 p = polynomialSphereL2 q ↔ p = q := by
  rw [← sub_eq_zero, ← map_sub,
    polynomialSphereL2_eq_zero_iff hF k (p - q) ((harmonicHomogeneous n k).sub_mem hp hq),
    sub_eq_zero]

lemma polynomialSphereL2_mem (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ harmonicHomogeneous n k) :
    polynomialSphereL2 p ∈ harmonicSphereSubspace n k :=
  ⟨p, hp, rfl⟩

lemma polynomialSphereL2_finite_pythagoras (hF : SphereFischerInner n)
    (hO : OrthogonalSphereHarmonics n) (s : Finset ℕ)
    (p : ℕ → MvPolynomial (Fin n) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous n k) :
    ‖∑ k ∈ s, polynomialSphereL2 (p k)‖ ^ 2 =
      ∑ k ∈ s, normalizedFischerSquare k (p k) := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro k hk
  rw [inner_sum]
  have hdiag : (∑ m ∈ s, ⟪polynomialSphereL2 (p k), polynomialSphereL2 (p m)⟫_ℝ) =
      ⟪polynomialSphereL2 (p k), polynomialSphereL2 (p k)⟫_ℝ := by
    apply Finset.sum_eq_single k
    · intro m hm hmk
      exact hO k m (Ne.symm hmk) _ (polynomialSphereL2_mem k (p k) (hp k hk))
        _ (polynomialSphereL2_mem m (p m) (hp m hm))
    · intro hn
      exact False.elim (hn hk)
  rw [hdiag, hF k (p k) (p k) (hp k hk) (hp k hk)]
  rfl

end OAI.AnisotropicCalderon.SphereHarmonic
