module

public import Proof.CalderonN.SphereDerivativeAdjoint
public import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Tactic

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
      LinearMap.ker (harmonicPolynomialDerivativeMap m i) := by
  intro p hp
  have hz : polynomialSphereL2 (p : MvPolynomial (Fin n) ℝ) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hp)
  have hpz := (polynomialSphereL2_eq_zero_iff hF (m+1) p p.property).mp hz
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change polynomialSphereL2 (pderiv i (p : MvPolynomial (Fin n) ℝ)) = 0
  rw [hpz,map_zero,map_zero]

def harmonicDerivativeLinear (hF : SphereFischerInner n) (m : ℕ) (i : Fin n) :
    harmonicSphereSubspace n (m+1) →ₗ[ℝ] harmonicSphereSubspace n m :=
  (harmonicPolynomialSphereMap (m+1)).liftOfSurjective
    (harmonicPolynomialSphereMap_surjective (m+1))
    ⟨harmonicPolynomialDerivativeMap m i,harmonicPolynomialSphereMap_ker_le_derivative hF m i⟩

lemma harmonicDerivativeLinear_apply_image (hF : SphereFischerInner n) (m : ℕ) (i : Fin n)
    (p : harmonicHomogeneous n (m+1)) :
    harmonicDerivativeLinear hF m i (harmonicPolynomialSphereMap (m+1) p) =
      harmonicPolynomialDerivativeMap m i p := by
  unfold harmonicDerivativeLinear
  exact LinearMap.equivOfSurjective_apply (harmonicPolynomialSphereMap_surjective (m+1))
    (harmonicPolynomialSphereMap_ker_le_derivative hF m i)

 
def harmonicDerivative (hF : SphereFischerInner n) (m : ℕ) (i : Fin n) :
    harmonicSphereSubspace n (m+1) →L[ℝ] harmonicSphereSubspace n m := by
  exact (harmonicDerivativeLinear hF m i).toContinuousLinearMap

lemma harmonicDerivative_apply_image (hF : SphereFischerInner n) (m : ℕ) (i : Fin n)
    (p : harmonicHomogeneous n (m+1)) :
    harmonicDerivative hF m i (harmonicPolynomialSphereMap (m+1) p) =
      harmonicPolynomialDerivativeMap m i p := harmonicDerivativeLinear_apply_image hF m i p

def harmonicPolynomialDerivativeAdjointMap (k : ℕ) (i : Fin n) :
    harmonicHomogeneous n k →ₗ[ℝ] harmonicSphereSubspace n (k+1) where
  toFun p := ⟨polynomialSphereL2 (sphereDerivativeAdjoint k i p),
    polynomialSphereL2_mem (k+1) _ (sphereDerivativeAdjoint_harmonicHomogeneous k i p p.property)⟩
  map_add' p q := by
    apply Subtype.ext
    change polynomialSphereL2 (sphereDerivativeAdjoint k i ((p : MvPolynomial (Fin n) ℝ)+q)) = _
    rw [sphereDerivativeAdjoint_add,map_add]
    rfl
  map_smul' c p := by
    apply Subtype.ext
    change polynomialSphereL2 (sphereDerivativeAdjoint k i (c • (p : MvPolynomial (Fin n) ℝ))) =
      c • polynomialSphereL2 (sphereDerivativeAdjoint k i (p : MvPolynomial (Fin n) ℝ))
    rw [smul_eq_C_mul,sphereDerivativeAdjoint_C_mul,← smul_eq_C_mul,map_smul]

lemma harmonicPolynomialSphereMap_ker_le_derivativeAdjoint (hF : SphereFischerInner n)
    (k : ℕ) (i : Fin n) :
    LinearMap.ker (harmonicPolynomialSphereMap k) ≤
      LinearMap.ker (harmonicPolynomialDerivativeAdjointMap k i) := by
  intro p hp
  have hz : polynomialSphereL2 (p : MvPolynomial (Fin n) ℝ) = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hp)
  have hpz := (polynomialSphereL2_eq_zero_iff hF k p p.property).mp hz
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change polynomialSphereL2 (sphereDerivativeAdjoint k i (p : MvPolynomial (Fin n) ℝ)) = 0
  rw [hpz,sphereDerivativeAdjoint_zero,map_zero]

def harmonicDerivativeAdjointLinear (hF : SphereFischerInner n) (k : ℕ) (i : Fin n) :
    harmonicSphereSubspace n k →ₗ[ℝ] harmonicSphereSubspace n (k+1) :=
  (harmonicPolynomialSphereMap k).liftOfSurjective (harmonicPolynomialSphereMap_surjective k)
    ⟨harmonicPolynomialDerivativeAdjointMap k i,harmonicPolynomialSphereMap_ker_le_derivativeAdjoint hF k i⟩

lemma harmonicDerivativeAdjointLinear_apply_image (hF : SphereFischerInner n) (k : ℕ) (i : Fin n)
    (p : harmonicHomogeneous n k) :
    harmonicDerivativeAdjointLinear hF k i (harmonicPolynomialSphereMap k p) =
      harmonicPolynomialDerivativeAdjointMap k i p := by
  unfold harmonicDerivativeAdjointLinear
  exact LinearMap.equivOfSurjective_apply (harmonicPolynomialSphereMap_surjective k)
    (harmonicPolynomialSphereMap_ker_le_derivativeAdjoint hF k i)

 
def harmonicDerivativeAdjoint (hF : SphereFischerInner n) (k : ℕ) (i : Fin n) :
    harmonicSphereSubspace n k →L[ℝ] harmonicSphereSubspace n (k+1) := by
  exact (harmonicDerivativeAdjointLinear hF k i).toContinuousLinearMap

lemma harmonicDerivativeAdjoint_apply_image (hF : SphereFischerInner n) (k : ℕ) (i : Fin n)
    (p : harmonicHomogeneous n k) :
    harmonicDerivativeAdjoint hF k i (harmonicPolynomialSphereMap k p) =
      harmonicPolynomialDerivativeAdjointMap k i p := harmonicDerivativeAdjointLinear_apply_image hF k i p

theorem inner_harmonicDerivativeAdjoint (hF : SphereFischerInner n) (k : ℕ) (i : Fin n)
    (u : harmonicSphereSubspace n k) (v : harmonicSphereSubspace n (k+1)) :
    ⟪harmonicDerivativeAdjoint hF k i u,v⟫_ℝ = ⟪u,harmonicDerivative hF k i v⟫_ℝ := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  rcases harmonicPolynomialSphereMap_surjective (k+1) v with ⟨q,rfl⟩
  rw [harmonicDerivativeAdjoint_apply_image,harmonicDerivative_apply_image]
  exact sphereDerivativeAdjoint_inner_adjoint hF k i p q p.property q.property

theorem harmonicDerivativeAdjoint_eq_adjoint (hF : SphereFischerInner n) (k : ℕ) (i : Fin n) :
    harmonicDerivativeAdjoint hF k i = ContinuousLinearMap.adjoint (harmonicDerivative hF k i) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [inner_harmonicDerivativeAdjoint,ContinuousLinearMap.adjoint_inner_left]

end CalderonN
