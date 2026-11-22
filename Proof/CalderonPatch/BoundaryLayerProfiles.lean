/-
Adapted from the conformal Poisson Lean formalization by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad, BSD 3-Clause.
Source: arxiv-2610.13592-lean commit 4cfcab036aedbb4f825a3aeb366da12fe5673ddd.
See the source and license in references/conformal-poisson-4cfcab03.
-/
module

public import Proof.CalderonPatch.BoundaryLayerPolynomial

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

public section

noncomputable section

open Set
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

structure BoundaryLayerCoefficients (ξ : Fin n → ℝ) (U : Set Y) where
  kappa : Y → ℝ
  inverse : ℕ → Fin n → Fin n → Y → ℂ
  normalDrift : ℕ → Y → ℂ
  tangentDrift : ℕ → Fin n → Y → ℂ
  kappa_smooth : ContDiffOn ℝ ∞ kappa U
  kappa_pos : ∀ y ∈ U, 0 < kappa y
  inverse_smooth : ∀ l i j, ContDiffOn ℝ ∞ (inverse l i j) U
  inverse_symm : ∀ l i j y, y ∈ U → inverse l i j y = inverse l j i y
  normalDrift_smooth : ∀ l, ContDiffOn ℝ ∞ (normalDrift l) U
  tangentDrift_smooth : ∀ l i, ContDiffOn ℝ ∞ (tangentDrift l i) U
  principal_squared : ∀ y ∈ U, (kappa y : ℂ) ^ 2 =
    ∑ i, ∑ j, inverse 0 i j y * (ξ i : ℂ) * (ξ j : ℂ)


end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure TriangularLayerSystem (U K : Set E) where
  forcing : ℕ → ℕ → (E → ℂ[X]) → E → ℂ[X]
  regular : ∀ j k, k < j → ∀ P : E → ℂ[X], CoeffContDiffOn P U →
    CoeffContDiffOn (forcing j k P) U
  degree : ∀ j k, k < j → ∀ P : E → ℂ[X],
    (∀ y ∈ U, (P y).natDegree ≤ 2 * k) →
    ∀ y ∈ U, (forcing j k P y).natDegree ≤ 2 * j - 1
  zero_outside : ∀ j k, k < j → ∀ P : E → ℂ[X],
    (∀ y ∉ K, P y = 0) → ∀ y ∉ K, forcing j k P y = 0

@[expose] def triangularLayerPolynomial (μ a : E → ℂ)
    (F : ℕ → ℕ → (E → ℂ[X]) → E → ℂ[X]) (j : ℕ) : E → ℂ[X] :=
  if j = 0 then fun y => C (a y)
  else fun y => fixedDegreeTransport (μ y) (2 * j)
    (-∑ k : Fin j, F j k.val (triangularLayerPolynomial μ a F k.val) y)
termination_by j

theorem triangularLayerPolynomial_zero (μ a : E → ℂ)
    (F : ℕ → ℕ → (E → ℂ[X]) → E → ℂ[X]) :
    triangularLayerPolynomial μ a F 0 = fun y => C (a y) := by
  rw [triangularLayerPolynomial]
  simp

theorem triangularLayerPolynomial_succ (μ a : E → ℂ)
    (F : ℕ → ℕ → (E → ℂ[X]) → E → ℂ[X]) (j : ℕ) :
    triangularLayerPolynomial μ a F (j + 1) = fun y =>
      fixedDegreeTransport (μ y) (2 * (j + 1))
        (-∑ k : Fin (j + 1), F (j + 1) k.val (triangularLayerPolynomial μ a F k.val) y) := by
  rw [triangularLayerPolynomial]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]

theorem triangularLayerPolynomial_properties
    {U K : Set E} (T : TriangularLayerSystem U K) (μ a : E → ℂ)
    (hμ : ContDiffOn ℝ ∞ μ U) (hμ0 : ∀ y ∈ U, μ y ≠ 0)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) :
    ∀ j : ℕ,
      CoeffContDiffOn (triangularLayerPolynomial μ a T.forcing j) U ∧
      (∀ y ∈ U, (triangularLayerPolynomial μ a T.forcing j y).natDegree ≤ 2 * j) ∧
      (∀ y ∉ K, triangularLayerPolynomial μ a T.forcing j y = 0) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      rw [triangularLayerPolynomial_zero]
      refine ⟨?_, ?_, ?_⟩
      · simpa only [monomial_zero_left] using CoeffContDiffOn.monomial ha 0
      · intro y hy
        simp
      · intro y hy
        simp [ha0 y hy]
    | succ j =>
      let R : E → ℂ[X] := fun y => -∑ k : Fin (j + 1),
        T.forcing (j + 1) k.val (triangularLayerPolynomial μ a T.forcing k.val) y
      have hR : CoeffContDiffOn R U := by
        have hs := CoeffContDiffOn.sum (univ : Finset (Fin (j + 1)))
          (fun k _ => T.regular (j + 1) k.val k.isLt _ (ih k.val k.isLt).1)
        simpa only [zero_sub] using (CoeffContDiffOn.const 0 U).sub hs
      have hRD (y : E) (hy : y ∈ U) : (R y).natDegree < 2 * (j + 1) := by
        have hs : (∑ k : Fin (j + 1),
            T.forcing (j + 1) k.val (triangularLayerPolynomial μ a T.forcing k.val) y).natDegree ≤
            2 * (j + 1) - 1 := by
          apply natDegree_sum_le_of_forall_le
          intro k hk
          exact T.degree (j + 1) k.val k.isLt _ (ih k.val k.isLt).2.1 y hy
        simpa only [R, natDegree_neg] using hs.trans_lt (by omega : 2 * (j + 1) - 1 < 2 * (j + 1))
      have hR0 (y : E) (hy : y ∉ K) : R y = 0 := by
        simp only [R, neg_eq_zero]
        apply Finset.sum_eq_zero
        intro k hk
        exact T.zero_outside (j + 1) k.val k.isLt _ (ih k.val k.isLt).2.2 y hy
      rw [triangularLayerPolynomial_succ]
      refine ⟨hR.fixedDegreeTransport hμ hμ0 (2 * (j + 1)), ?_, ?_⟩
      · intro y hy
        exact fixedDegreeTransport_natDegree_le _ _ _ (hRD y hy)
      · intro y hy
        change fixedDegreeTransport (μ y) (2 * (j + 1)) (R y) = 0
        rw [hR0 y hy, fixedDegreeTransport_zero]

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def totalLayerForcing (μ a : E → ℂ)
    (F : ℕ → ℕ → (E → ℂ[X]) → E → ℂ[X]) (j : ℕ) (y : E) : ℂ[X] :=
  -∑ k : Fin j, F j k.val (triangularLayerPolynomial μ a F k.val) y

theorem totalLayerForcing_degree
    {U K : Set E} (T : TriangularLayerSystem U K) (μ a : E → ℂ)
    (hμ : ContDiffOn ℝ ∞ μ U) (hμ0 : ∀ y ∈ U, μ y ≠ 0)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) (hj : 0 < j) {y : E} (hy : y ∈ U) :
    (totalLayerForcing μ a T.forcing j y).natDegree < 2 * j := by
  have hs : (∑ k : Fin j, T.forcing j k.val
      (triangularLayerPolynomial μ a T.forcing k.val) y).natDegree ≤ 2 * j - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact T.degree j k.val k.isLt _
      (triangularLayerPolynomial_properties T μ a hμ hμ0 ha ha0 k.val).2.1 y hy
  simpa only [totalLayerForcing, natDegree_neg] using hs.trans_lt (by omega : 2 * j - 1 < 2 * j)

theorem triangularLayerPolynomial_transport
    {U K : Set E} (T : TriangularLayerSystem U K) (μ a : E → ℂ)
    (hμ : ContDiffOn ℝ ∞ μ U) (hμ0 : ∀ y ∈ U, μ y ≠ 0)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) (hj : 0 < j) {y : E} (hy : y ∈ U) :
    C (μ y) * derivative (triangularLayerPolynomial μ a T.forcing j y) -
      derivative (derivative (triangularLayerPolynomial μ a T.forcing j y)) =
        totalLayerForcing μ a T.forcing j y := by
  rw [triangularLayerPolynomial, if_neg (Nat.ne_of_gt hj)]
  exact fixedDegreeTransport_equation (μ y) (hμ0 y hy) (2 * j) _
    (totalLayerForcing_degree T μ a hμ hμ0 ha ha0 j hj hy)

theorem triangularLayerPolynomial_face_zero
    (μ a : E → ℂ) (F : ℕ → ℕ → (E → ℂ[X]) → E → ℂ[X])
    (j : ℕ) (hj : 0 < j) (y : E) : (triangularLayerPolynomial μ a F j y).eval 0 = 0 := by
  rw [triangularLayerPolynomial, if_neg (Nat.ne_of_gt hj)]
  exact polynomialPrimitive_zero _

theorem triangularLayerPolynomial_trace
    {U K : Set E} (T : TriangularLayerSystem U K) (μ a : E → ℂ)
    (hμ : ContDiffOn ℝ ∞ μ U) (hμ0 : ∀ y ∈ U, μ y ≠ 0)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) (hj : 0 < j) {y : E} (hy : y ∈ U) :
    (derivative (triangularLayerPolynomial μ a T.forcing j y)).eval 0 =
      polynomialTrace (μ y) (totalLayerForcing μ a T.forcing j y) := by
  have hD := totalLayerForcing_degree T μ a hμ hμ0 ha ha0 j hj hy
  rw [polynomialTrace_eq_of_degree_lt (μ y) (hμ0 y hy) _ (2 * j) hD]
  rw [triangularLayerPolynomial, if_neg (Nat.ne_of_gt hj)]
  exact congrArg (Polynomial.eval 0) (polynomialPrimitive_derivative _)

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem profileDerivative_natDegree_le (κ : ℝ) (p : ℂ[X]) :
    (profileDerivative κ p).natDegree ≤ p.natDegree := by
  apply (natDegree_sub_le _ _).trans
  exact max_le ((natDegree_derivative_le p).trans (Nat.sub_le _ _)) (natDegree_C_mul_le _ _)

theorem CoeffContDiffOn.normalProfileDerivative
    {U : Set Y} {P : Y → ℂ[X]} {κ : Y → ℝ}
    (hP : CoeffContDiffOn P U) (hκ : ContDiffOn ℝ ∞ κ U) :
    CoeffContDiffOn (fun y => profileDerivative (κ y) (P y)) U :=
  hP.derivative.sub (hP.C_mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hκ))

namespace BoundaryLayerCoefficients

@[expose] def principalTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l : ℕ) (P : Y → ℂ[X]) (y : Y) : ℂ[X] :=
  C (∑ i, ∑ j, B.inverse l i j y * (ξ i : ℂ) * (ξ j : ℂ)) * X ^ l * P y

@[expose] def normalTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l : ℕ) (P : Y → ℂ[X]) (y : Y) : ℂ[X] :=
  C (B.normalDrift (l - 1) y / 2) * X ^ (l - 1) * profileDerivative (B.kappa y) (P y)

@[expose] def crossTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l d : ℕ) (P : Y → ℂ[X]) (y : Y) : ℂ[X] :=
  C (-2 * Complex.I) * ∑ i, ∑ j,
    C (B.inverse (l - 1) i j y * (ξ i : ℂ)) * X ^ (l - 1) *
      profileSpatialDeriv d (e j) B.kappa P y

@[expose] def phaseDriftTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l : ℕ) (P : Y → ℂ[X]) (y : Y) : ℂ[X] :=
  C (-Complex.I) * ∑ i,
    C (B.tangentDrift (l - 1) i y * (ξ i : ℂ)) * X ^ (l - 1) * P y

@[expose] def tangentSecondTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l d : ℕ) (P : Y → ℂ[X]) (y : Y) : ℂ[X] :=
  -(∑ i, ∑ j, C (B.inverse (l - 2) i j y) * X ^ (l - 2) *
    profileSpatialDeriv (d + 1) (e i) B.kappa (profileSpatialDeriv d (e j) B.kappa P) y)

@[expose] def tangentFirstTerm {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l d : ℕ) (P : Y → ℂ[X]) (y : Y) : ℂ[X] :=
  -(∑ i, C (B.tangentDrift (l - 2) i y) * X ^ (l - 2) *
    profileSpatialDeriv d (e i) B.kappa P y)

@[expose] def forcing {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (j k : ℕ) (P : Y → ℂ[X]) (y : Y) : ℂ[X] :=
  let l := j - k
  B.principalTerm l P y + B.normalTerm l P y + B.crossTerm l (2 * k) P y +
    B.phaseDriftTerm l P y +
    (if 2 ≤ l then B.tangentSecondTerm l (2 * k) P y + B.tangentFirstTerm l (2 * k) P y else 0)

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem principalTerm_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.principalTerm l P) U := by
  have hc : ContDiffOn ℝ ∞
      (fun y => ∑ i, ∑ j, B.inverse l i j y * (ξ i : ℂ) * (ξ j : ℂ)) U :=
    ContDiffOn.sum (fun i _ => ContDiffOn.sum
      (fun j _ => ((B.inverse_smooth l i j).mul contDiffOn_const).mul contDiffOn_const))
  exact ((CoeffContDiffOn.const (X ^ l) U).C_mul hc).mul hP

theorem normalTerm_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.normalTerm l P) U :=
  ((CoeffContDiffOn.const (X ^ (l - 1)) U).C_mul ((B.normalDrift_smooth (l - 1)).div_const (2 : ℂ))).mul
    (hP.normalProfileDerivative B.kappa_smooth)

theorem crossTerm_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (hU : IsOpen U) (l d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.crossTerm l d P) U := by
  apply CoeffContDiffOn.C_mul
  · apply CoeffContDiffOn.sum
    intro i hi
    apply CoeffContDiffOn.sum
    intro j hj
    exact ((CoeffContDiffOn.const (X ^ (l - 1)) U).C_mul
      ((B.inverse_smooth (l - 1) i j).mul contDiffOn_const)).mul
        (hP.profileSpatialDeriv hU B.kappa_smooth d (e j))
  · exact contDiffOn_const

theorem phaseDriftTerm_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (l : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.phaseDriftTerm l P) U := by
  apply CoeffContDiffOn.C_mul
  · apply CoeffContDiffOn.sum
    intro i hi
    exact ((CoeffContDiffOn.const (X ^ (l - 1)) U).C_mul
      ((B.tangentDrift_smooth (l - 1) i).mul contDiffOn_const)).mul hP
  · exact contDiffOn_const

theorem tangentSecondTerm_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (hU : IsOpen U) (l d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.tangentSecondTerm l d P) U := by
  have hs : CoeffContDiffOn (fun y => ∑ i, ∑ j, C (B.inverse (l - 2) i j y) * X ^ (l - 2) *
      profileSpatialDeriv (d + 1) (e i) B.kappa (profileSpatialDeriv d (e j) B.kappa P) y) U := by
    apply CoeffContDiffOn.sum
    intro i hi
    apply CoeffContDiffOn.sum
    intro j hj
    exact ((CoeffContDiffOn.const (X ^ (l - 2)) U).C_mul (B.inverse_smooth (l - 2) i j)).mul
      ((hP.profileSpatialDeriv hU B.kappa_smooth d (e j)).profileSpatialDeriv hU B.kappa_smooth (d + 1) (e i))
  unfold tangentSecondTerm
  simpa only [zero_sub] using (CoeffContDiffOn.const 0 U).sub hs

theorem tangentFirstTerm_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (hU : IsOpen U) (l d : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.tangentFirstTerm l d P) U := by
  have hs : CoeffContDiffOn (fun y => ∑ i, C (B.tangentDrift (l - 2) i y) * X ^ (l - 2) *
      profileSpatialDeriv d (e i) B.kappa P y) U := by
    apply CoeffContDiffOn.sum
    intro i hi
    exact ((CoeffContDiffOn.const (X ^ (l - 2)) U).C_mul (B.tangentDrift_smooth (l - 2) i)).mul
      (hP.profileSpatialDeriv hU B.kappa_smooth d (e i))
  unfold tangentFirstTerm
  simpa only [zero_sub] using (CoeffContDiffOn.const 0 U).sub hs

theorem forcing_regular {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (hU : IsOpen U) (j k : ℕ) {P : Y → ℂ[X]} (hP : CoeffContDiffOn P U) :
    CoeffContDiffOn (B.forcing j k P) U := by
  have hbase := (((B.principalTerm_regular (j - k) hP).add (B.normalTerm_regular (j - k) hP)).add
    (B.crossTerm_regular hU (j - k) (2 * k) hP)).add (B.phaseDriftTerm_regular (j - k) hP)
  unfold forcing
  dsimp only
  by_cases h : 2 ≤ j - k
  · simpa only [ite_eq_left h] using hbase.add
      ((B.tangentSecondTerm_regular hU (j - k) (2 * k) hP).add
        (B.tangentFirstTerm_regular hU (j - k) (2 * k) hP))
  · simpa only [ite_eq_right h, add_zero] using hbase

theorem forcing_zero_outside {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (j k : ℕ) (P : Y → ℂ[X]) {K : Set Y} (hK : IsClosed K)
    (hP0 : ∀ y ∉ K, P y = 0) {y : Y} (hy : y ∉ K) : B.forcing j k P y = 0 := by
  have hd (i : Fin n) : profileSpatialDeriv (2 * k) (EuclideanSpace.single i 1) B.kappa P y = 0 :=
    profileSpatialDeriv_zero_outside _ _ _ _ hK hP0 hy
  have hdd (i j : Fin n) : profileSpatialDeriv (2 * k + 1) (EuclideanSpace.single i 1) B.kappa
      (profileSpatialDeriv (2 * k) (EuclideanSpace.single j 1) B.kappa P) y = 0 :=
    profileSpatialDeriv_zero_outside _ _ _ _ hK
      (fun x hx => profileSpatialDeriv_zero_outside _ _ _ _ hK hP0 hx) hy
  simp [forcing, principalTerm, normalTerm, crossTerm, phaseDriftTerm, tangentSecondTerm,
    tangentFirstTerm, hP0 y hy, profileDerivative, hd, hdd]

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer

theorem scalar_X_pow_mul_degree_le (c : ℂ) (l d : ℕ) (p : ℂ[X]) (hp : p.natDegree ≤ d) :
    (C c * X ^ l * p).natDegree ≤ l + d := by
  have hc : (C c * X ^ l).natDegree ≤ l :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
  exact (natDegree_mul_le : (C c * X ^ l * p).natDegree ≤ _).trans (add_le_add hc hp)

namespace BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem principalTerm_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l d : ℕ) (P : Y → ℂ[X]) {y : Y} (hp : (P y).natDegree ≤ d) :
    (B.principalTerm l P y).natDegree ≤ l + d :=
  scalar_X_pow_mul_degree_le _ _ _ _ hp

theorem normalTerm_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l d : ℕ) (P : Y → ℂ[X]) {y : Y} (hp : (P y).natDegree ≤ d) :
    (B.normalTerm l P y).natDegree ≤ l + d := by
  have he := scalar_X_pow_mul_degree_le (B.normalDrift (l - 1) y / 2) (l - 1) d
    (profileDerivative (B.kappa y) (P y)) ((profileDerivative_natDegree_le _ _).trans hp)
  exact he.trans (Nat.add_le_add_right (Nat.sub_le _ _) _)

theorem crossTerm_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l d : ℕ) (hl : 1 ≤ l) (P : Y → ℂ[X]) {y : Y} (hp : (P y).natDegree ≤ d) :
    (B.crossTerm l d P y).natDegree ≤ l + d := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (scalar_X_pow_mul_degree_le _ (l - 1) (d + 1) _
    (profileSpatialDeriv_natDegree_le d (e j) B.kappa P hp)).trans (by omega)

theorem phaseDriftTerm_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l d : ℕ) (P : Y → ℂ[X]) {y : Y} (hp : (P y).natDegree ≤ d) :
    (B.phaseDriftTerm l P y).natDegree ≤ l + d := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (scalar_X_pow_mul_degree_le _ (l - 1) d _ hp).trans (by omega)

theorem tangentSecondTerm_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l d : ℕ) (hl : 2 ≤ l) (P : Y → ℂ[X]) {y : Y} (hp : (P y).natDegree ≤ d) :
    (B.tangentSecondTerm l d P y).natDegree ≤ l + d := by
  rw [tangentSecondTerm, natDegree_neg]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have h₁ := profileSpatialDeriv_natDegree_le d (e j) B.kappa P hp
  have h₂ := profileSpatialDeriv_natDegree_le (d + 1) (e i) B.kappa
    (profileSpatialDeriv d (e j) B.kappa P) h₁
  exact (scalar_X_pow_mul_degree_le _ (l - 2) (d + 1 + 1) _ h₂).trans (by omega)

theorem tangentFirstTerm_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (l d : ℕ) (hl : 2 ≤ l) (P : Y → ℂ[X]) {y : Y} (hp : (P y).natDegree ≤ d) :
    (B.tangentFirstTerm l d P y).natDegree ≤ l + d := by
  rw [tangentFirstTerm, natDegree_neg]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (scalar_X_pow_mul_degree_le _ (l - 2) (d + 1) _
    (profileSpatialDeriv_natDegree_le d (e i) B.kappa P hp)).trans (by omega)

theorem forcing_degree {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (j k : ℕ) (hkj : k < j) (P : Y → ℂ[X]) {y : Y} (hp : (P y).natDegree ≤ 2 * k) :
    (B.forcing j k P y).natDegree ≤ 2 * j - 1 := by
  have hbase := natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (B.principalTerm_degree (j - k) (2 * k) P hp)
        (B.normalTerm_degree (j - k) (2 * k) P hp))
      (B.crossTerm_degree (j - k) (2 * k) (by omega) P hp))
    (B.phaseDriftTerm_degree (j - k) (2 * k) P hp)
  have he : (B.forcing j k P y).natDegree ≤ j - k + 2 * k := by
    by_cases h : 2 ≤ j - k
    · simp only [forcing, ite_eq_left h]
      exact natDegree_add_le_of_degree_le hbase (natDegree_add_le_of_degree_le
        (B.tangentSecondTerm_degree (j - k) (2 * k) h P hp)
        (B.tangentFirstTerm_degree (j - k) (2 * k) h P hp))
    · simpa only [forcing, ite_eq_right h, add_zero] using hbase
  exact he.trans (by omega)

end BoundaryLayerCoefficients
end CalderonPatch.BoundaryLayer

open Polynomial Set Filter Topology
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[expose] def cutoffProfileFamily (η : ℝ → ℝ) (κ : E → ℝ) (P : E → ℂ[X]) (h : ℝ) (x : E × ℝ) : ℂ :=
  η x.2 • polynomialProfileFamily κ P (x.1, x.2 / h)

theorem cutoffProfileFamily_tsupport_subset
    (η : ℝ → ℝ) (κ : E → ℝ) (P : E → ℂ[X]) (h : ℝ)
    {K : Set E} (hK : IsClosed K) (hP0 : ∀ y ∉ K, P y = 0) :
    tsupport (cutoffProfileFamily η κ P h) ⊆ K ×ˢ tsupport η := by
  apply closure_minimal _ (hK.prod (isClosed_tsupport η))
  intro x hx
  constructor
  · by_contra hy
    have he := hP0 x.1 hy
    exact hx (by simp [cutoffProfileFamily, polynomialProfileFamily, he])
  · by_contra ht
    have he := image_eq_zero_of_notMem_tsupport ht
    exact hx (by simp [cutoffProfileFamily, he])

theorem cutoffProfileFamily_hasCompactSupport
    (η : ℝ → ℝ) (κ : E → ℝ) (P : E → ℂ[X]) (h : ℝ)
    {K : Set E} (hK : IsCompact K) (hη : HasCompactSupport η) (hP0 : ∀ y ∉ K, P y = 0) :
    HasCompactSupport (cutoffProfileFamily η κ P h) :=
  (hK.prod hη).of_isClosed_subset (isClosed_tsupport _)
    (cutoffProfileFamily_tsupport_subset η κ P h hK.isClosed hP0)

theorem cutoffProfileFamily_contDiff
    {η : ℝ → ℝ} {κ : E → ℝ} {P : E → ℂ[X]} {U : Set E} (hU : IsOpen U)
    (hη : ContDiff ℝ ∞ η) (hκ : ContDiffOn ℝ ∞ κ U) (hP : CoeffContDiffOn P U)
    (D : ℕ) (hD : ∀ y ∈ U, (P y).natDegree < D)
    {K : Set E} (hK : IsClosed K) (hKU : K ⊆ U) (hP0 : ∀ y ∉ K, P y = 0) (h : ℝ) :
    ContDiff ℝ ∞ (cutoffProfileFamily η κ P h) := by
  have hmap : ContDiff ℝ ∞ (fun x : E × ℝ => (x.1, x.2 / h)) :=
    contDiff_fst.prodMk (contDiff_snd.div_const h)
  have hOn : ContDiffOn ℝ ∞ (cutoffProfileFamily η κ P h) (U ×ˢ Set.univ) :=
    (hη.comp_contDiffOn contDiffOn_snd).smul
      ((hP.profile hκ D hD).comp hmap.contDiffOn
        (fun x (hx : x ∈ U ×ˢ (univ : Set ℝ)) => ⟨hx.1, mem_univ _⟩))
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport (cutoffProfileFamily η κ P h)
  · have hy := (cutoffProfileFamily_tsupport_subset η κ P h hK hP0 hx).1
    exact (hOn x ⟨hKU hy, mem_univ _⟩).contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hKU hy, mem_univ _⟩)
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

end CalderonPatch.BoundaryLayer

open Polynomial Set Finset
open scoped ContDiff
namespace CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
variable {n : ℕ}
local notation "Y" => EuclideanSpace ℝ (Fin n)

@[expose] def transportSystem {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) (K : Set Y) (hK : IsClosed K) : TriangularLayerSystem U K where
  forcing := B.forcing
  regular j k _ P hP := B.forcing_regular hU j k hP
  degree j k hkj P hP y hy := B.forcing_degree j k hkj P (hP y hy)
  zero_outside j k _ P hP y hy := B.forcing_zero_outside j k P hK hP hy

@[expose] def transportScale {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) (y : Y) : ℂ :=
  2 * (B.kappa y : ℂ)

theorem transportScale_smooth {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U) :
    ContDiffOn ℝ ∞ B.transportScale U :=
  contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn B.kappa_smooth)

theorem transportScale_ne_zero {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    {y : Y} (hy : y ∈ U) : B.transportScale y ≠ 0 :=
  mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (B.kappa_pos y hy).ne')

@[expose] def layerPolynomial {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) : Y → ℂ[X] :=
  triangularLayerPolynomial B.transportScale a B.forcing j

@[expose] def layerForcing {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) : Y → ℂ[X] :=
  totalLayerForcing B.transportScale a B.forcing j

theorem layerPolynomial_properties {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) :
    CoeffContDiffOn (B.layerPolynomial a j) U ∧
      (∀ y ∈ U, (B.layerPolynomial a j y).natDegree ≤ 2 * j) ∧
      (∀ y ∉ K, B.layerPolynomial a j y = 0) :=
  triangularLayerPolynomial_properties (B.transportSystem hU K hK) B.transportScale a
    B.transportScale_smooth (fun y hy => B.transportScale_ne_zero hy) ha ha0 j

theorem layerPolynomial_zero {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (y : Y) : B.layerPolynomial a 0 y = C (a y) := by
  exact congrFun (triangularLayerPolynomial_zero B.transportScale a B.forcing) y

theorem layerPolynomial_transport {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) (hj : 0 < j) {y : Y} (hy : y ∈ U) :
    C (2 * (B.kappa y : ℂ)) * derivative (B.layerPolynomial a j y) -
      derivative (derivative (B.layerPolynomial a j y)) = B.layerForcing a j y :=
  triangularLayerPolynomial_transport (B.transportSystem hU K hK) B.transportScale a
    B.transportScale_smooth (fun y hy => B.transportScale_ne_zero hy) ha ha0 j hj hy

theorem layerPolynomial_face_zero {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) (hj : 0 < j) (y : Y) : (B.layerPolynomial a j y).eval 0 = 0 :=
  triangularLayerPolynomial_face_zero B.transportScale a B.forcing j hj y

@[expose] def profile {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) (x : Y × ℝ) : ℂ :=
  polynomialProfile (B.kappa x.1) (B.layerPolynomial a j x.1) x.2

theorem profile_contDiffOn {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) :
    ContDiffOn ℝ ∞ (B.profile a j) (U ×ˢ Set.univ) :=
  ((B.layerPolynomial_properties hU hK a ha ha0 j).1).profile B.kappa_smooth (2 * j + 1)
    (fun y hy => Nat.lt_succ_of_le ((B.layerPolynomial_properties hU hK a ha ha0 j).2.1 y hy))

theorem profile_transport {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (j : ℕ) (hj : 0 < j) {y : Y} (hy : y ∈ U) (s : ℝ) :
    -deriv (deriv (fun t => B.profile a j (y, t))) s +
      B.kappa y ^ 2 • B.profile a j (y, s) = polynomialProfile (B.kappa y) (B.layerForcing a j y) s := by
  change -deriv (deriv (polynomialProfile (B.kappa y) (B.layerPolynomial a j y))) s +
    B.kappa y ^ 2 • polynomialProfile (B.kappa y) (B.layerPolynomial a j y) s = _
  rw [secondOrder_polynomialProfile, B.layerPolynomial_transport hU hK a ha ha0 j hj hy]

theorem profile_face_zero {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (j : ℕ) (hj : 0 < j) (y : Y) : B.profile a j (y, 0) = 0 := by
  simp only [profile, polynomialProfile, mul_zero, Real.exp_zero, one_smul, Complex.ofReal_zero,
    B.layerPolynomial_face_zero a j hj y]

theorem cutoffProfile_contDiff {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsClosed K) (hKU : K ⊆ U) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (h : ℝ) :
    ContDiff ℝ ∞ (cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h) :=
  cutoffProfileFamily_contDiff hU hη B.kappa_smooth (B.layerPolynomial_properties hU hK a ha ha0 j).1
    (2 * j + 1) (fun y hy => Nat.lt_succ_of_le ((B.layerPolynomial_properties hU hK a ha ha0 j).2.1 y hy))
    hK hKU (B.layerPolynomial_properties hU hK a ha ha0 j).2.2 h

theorem cutoffProfile_hasCompactSupport {ξ : Fin n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (hU : IsOpen U) {K : Set Y} (hK : IsCompact K) (a : Y → ℂ)
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ)
    (η : ℝ → ℝ) (hη : HasCompactSupport η) (h : ℝ) :
    HasCompactSupport (cutoffProfileFamily η B.kappa (B.layerPolynomial a j) h) :=
  cutoffProfileFamily_hasCompactSupport η B.kappa _ h hK hη
    (B.layerPolynomial_properties hU hK.isClosed a ha ha0 j).2.2

end CalderonPatch.BoundaryLayer.BoundaryLayerCoefficients
