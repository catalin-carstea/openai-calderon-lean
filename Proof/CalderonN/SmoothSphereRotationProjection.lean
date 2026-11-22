module

public import Proof.CalderonN.SmoothAngularCasimir
import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace CalderonN
open OAI.AnisotropicCalderon AngularPolynomial SphereHarmonic SmoothSphereRotation GreenRadialTrace
variable {n : ℕ} [NeZero n]

lemma polynomialRotation_harmonicHomogeneous (k : ℕ) (hk : 1 ≤ k) (i j : Fin n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ∈ harmonicHomogeneous n k) :
    polynomialRotation i j p ∈ harmonicHomogeneous n k := by
  refine ⟨?_, ?_⟩
  · have hi := (isHomogeneous_X (R := ℝ) i).mul (hp.1.pderiv (i := j))
    have hj := (isHomogeneous_X (R := ℝ) j).mul (hp.1.pderiv (i := i))
    have hdeg : 1 + (k - 1) = k := by omega
    simpa only [polynomialRotation, hdeg] using hi.sub hj
  · rw [polynomialRotation, laplacian_sub, laplacian_X_mul, laplacian_X_mul,
      laplacian_pderiv, laplacian_pderiv, hp.2, map_zero, map_zero, mul_zero,
      mul_zero, zero_add, zero_add, pderiv_pderiv_comm i j]
    exact sub_self _

lemma polynomialRotation_harmonic_all (k : ℕ) (i j : Fin n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ∈ harmonicHomogeneous n k) :
    polynomialRotation i j p ∈ harmonicHomogeneous n k := by
  cases k with
  | zero =>
      rw [eq_C_of_mem_harmonicHomogeneous_zero hp]
      simp only [polynomialRotation,pderiv_C,mul_zero,sub_self]
      exact (harmonicHomogeneous n 0).zero_mem
  | succ k => exact polynomialRotation_harmonicHomogeneous _ (by omega) i j p hp

lemma smoothSphereLift_rotation_polynomial (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    smoothSphereLift (sphereRotationDerivative i j (polynomialEvaluation p))
      (contDiff_sphereRotationDerivative i j _ (contDiff_polynomialEvaluation p)) =
        polynomialSphereL2 (polynomialRotation i j p) := by
  change (ContinuousMap.toLp 2 (unitSphereProbability n) ℝ) _ =
    (ContinuousMap.toLp 2 (unitSphereProbability n) ℝ) _
  congr 1
  ext u
  exact congrFun (sphereRotationDerivative_polynomialEvaluation i j p) u.val

 
lemma polynomialSphereL2_rotation_skew (i j : Fin n) (p q : MvPolynomial (Fin n) ℝ) :
    ⟪polynomialSphereL2 (polynomialRotation i j p),polynomialSphereL2 q⟫_ℝ =
      -⟪polynomialSphereL2 p,polynomialSphereL2 (polynomialRotation i j q)⟫_ℝ := by
  have h := inner_sphereRotationDerivative_skew i j (polynomialEvaluation p)
    (polynomialEvaluation q) (contDiff_polynomialEvaluation p) (contDiff_polynomialEvaluation q)
  rw [smoothSphereLift_rotation_polynomial i j p,smoothSphereLift_polynomialEvaluation q,
    smoothSphereLift_polynomialEvaluation p,smoothSphereLift_rotation_polynomial i j q] at h
  exact h

 
lemma polynomialSphereL2_rotation_eq_zero_of_eq_zero (i j : Fin n)
    (p : MvPolynomial (Fin n) ℝ) (hp : polynomialSphereL2 p = 0) :
    polynomialSphereL2 (polynomialRotation i j p) = 0 := by
  have hn : ‖polynomialSphereL2 (polynomialRotation i j p)‖^2 = 0 := by
    rw [← real_inner_self_eq_norm_sq,polynomialSphereL2_rotation_skew i j p
      (polynomialRotation i j p),hp,inner_zero_left,neg_zero]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

def polynomialRotationLinear (i j : Fin n) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun := polynomialRotation i j
  map_add' p q := by simp [polynomialRotation,map_add,mul_add,sub_add_sub_comm]
  map_smul' c p := by
    simp only [polynomialRotation,smul_eq_C_mul,pderiv_C_mul,RingHom.id_apply]
    ring

 
def harmonicPolynomialSphereMap (k : ℕ) :
    harmonicHomogeneous n k →ₗ[ℝ] harmonicSphereSubspace n k :=
  ((polynomialSphereL2 (n := n)).comp (harmonicHomogeneous n k).subtype).codRestrict
    (harmonicSphereSubspace n k) (fun p => Submodule.mem_map_of_mem p.property)

lemma harmonicPolynomialSphereMap_surjective (k : ℕ) :
    Function.Surjective (harmonicPolynomialSphereMap (n := n) k) := by
  intro v
  rcases Submodule.mem_map.mp v.property with ⟨p,hp,hpv⟩
  refine ⟨⟨p,hp⟩,?_⟩
  apply Subtype.ext
  exact hpv

 
def rotatedHarmonicSphereMap (k : ℕ) (i j : Fin n) :
    harmonicHomogeneous n k →ₗ[ℝ] harmonicSphereSubspace n k :=
  (((polynomialSphereL2 (n := n)).comp (polynomialRotationLinear i j)).comp
    (harmonicHomogeneous n k).subtype).codRestrict (harmonicSphereSubspace n k)
    (fun p => Submodule.mem_map_of_mem (polynomialRotation_harmonic_all k i j p.val p.property))

lemma harmonicPolynomialSphereMap_ker_le_rotated (k : ℕ) (i j : Fin n) :
    LinearMap.ker (harmonicPolynomialSphereMap k) ≤
      LinearMap.ker (rotatedHarmonicSphereMap k i j) := by
  intro p hp
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  have hz := congrArg Subtype.val (LinearMap.mem_ker.mp hp)
  change polynomialSphereL2 (p : MvPolynomial (Fin n) ℝ) = 0 at hz
  exact polynomialSphereL2_rotation_eq_zero_of_eq_zero i j p hz

 
def harmonicSphereRotationLinear (k : ℕ) (i j : Fin n) :
    harmonicSphereSubspace n k →ₗ[ℝ] harmonicSphereSubspace n k :=
  (harmonicPolynomialSphereMap k).liftOfSurjective (harmonicPolynomialSphereMap_surjective k)
    ⟨rotatedHarmonicSphereMap k i j,harmonicPolynomialSphereMap_ker_le_rotated k i j⟩

lemma harmonicSphereRotationLinear_apply_image (k : ℕ) (i j : Fin n)
    (p : harmonicHomogeneous n k) :
    harmonicSphereRotationLinear k i j (harmonicPolynomialSphereMap k p) =
      rotatedHarmonicSphereMap k i j p := by
  unfold harmonicSphereRotationLinear
  exact LinearMap.equivOfSurjective_apply (harmonicPolynomialSphereMap_surjective k)
    (harmonicPolynomialSphereMap_ker_le_rotated k i j)

 
def harmonicSphereRotation (k : ℕ) (i j : Fin n) :
    harmonicSphereSubspace n k →L[ℝ] harmonicSphereSubspace n k := by
  exact LinearMap.toContinuousLinearMap (harmonicSphereRotationLinear k i j)

lemma harmonicSphereRotation_apply_image (k : ℕ) (i j : Fin n)
    (p : harmonicHomogeneous n k) :
    harmonicSphereRotation k i j (harmonicPolynomialSphereMap k p) =
      rotatedHarmonicSphereMap k i j p :=
  harmonicSphereRotationLinear_apply_image k i j p

lemma inner_harmonicSphereRotation_skew (k : ℕ) (i j : Fin n)
    (u v : harmonicSphereSubspace n k) :
    ⟪harmonicSphereRotation k i j u,v⟫_ℝ = -⟪u,harmonicSphereRotation k i j v⟫_ℝ := by
  rcases harmonicPolynomialSphereMap_surjective k u with ⟨p,rfl⟩
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨q,rfl⟩
  rw [harmonicSphereRotation_apply_image,harmonicSphereRotation_apply_image]
  change ⟪polynomialSphereL2 (polynomialRotation i j p),polynomialSphereL2 q⟫_ℝ =
    -⟪polynomialSphereL2 p,polynomialSphereL2 (polynomialRotation i j q)⟫_ℝ
  exact polynomialSphereL2_rotation_skew i j p q

 
theorem harmonicProjection_sphereRotationDerivative (k : ℕ) (i j : Fin n) (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    harmonicProjection k
      (smoothSphereLift (sphereRotationDerivative i j F) (contDiff_sphereRotationDerivative i j F hF)) =
        harmonicSphereRotation k i j (harmonicProjection k (smoothSphereLift F hF)) := by
  apply ext_inner_right ℝ
  intro v
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
  rw [harmonicProjection_inner k _ (harmonicPolynomialSphereMap k p),
    inner_harmonicSphereRotation_skew,
    harmonicProjection_inner k _
      (harmonicSphereRotation k i j (harmonicPolynomialSphereMap k p)),
    harmonicSphereRotation_apply_image]
  change ⟪smoothSphereLift (sphereRotationDerivative i j F)
      (contDiff_sphereRotationDerivative i j F hF),polynomialSphereL2 p⟫_ℝ =
    -⟪smoothSphereLift F hF,polynomialSphereL2 (polynomialRotation i j p)⟫_ℝ
  have h := inner_sphereRotationDerivative_skew i j F (polynomialEvaluation p)
    hF (contDiff_polynomialEvaluation (p : MvPolynomial (Fin n) ℝ))
  rw [smoothSphereLift_polynomialEvaluation (p : MvPolynomial (Fin n) ℝ),
    smoothSphereLift_rotation_polynomial i j (p : MvPolynomial (Fin n) ℝ)] at h
  exact h

lemma harmonicSphereRotation_self (k : ℕ) (i : Fin n) : harmonicSphereRotation k i i = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
  rw [harmonicSphereRotation_apply_image]
  apply Subtype.ext
  change polynomialSphereL2 (polynomialRotation i i p) = 0
  simp [polynomialRotation]

lemma harmonicSphereRotation_degree_zero (i j : Fin n) : harmonicSphereRotation 0 i j = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  rcases harmonicPolynomialSphereMap_surjective 0 v with ⟨p,rfl⟩
  rw [harmonicSphereRotation_apply_image]
  apply Subtype.ext
  change polynomialSphereL2 (polynomialRotation i j p) = 0
  rw [eq_C_of_mem_harmonicHomogeneous_zero p.property]
  simp [polynomialRotation]

end CalderonN
