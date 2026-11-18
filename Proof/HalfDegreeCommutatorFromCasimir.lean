import Proof.Archive.FinitePhysicalCasimirOperatorAssembly
import Proof.Archive.FiniteHarmonicDegreeNormalizedDirectionLift
import Proof.Archive.SphereSobolevDegreeFormPointCompletion
import Proof.Geometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.RotationCasimirEstimate
open OAI.AnisotropicCalderon.SpectralSylvester
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

/-- The supplied finite spectral estimates complete a degree commutator on
    the balanced half endpoints. The remaining native producer must supply
    the exact Casimir identity for its SAME rotation commutators and adjoints. -/
theorem exists_half_degree_commutator_of_casimir_identity
    (T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (K : ∀ m n : ℕ,harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (hCoeff : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (T (sphereSobolevSingleL (3/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • K m n z)
    (P Q : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (MP MQ : ℝ) (hMP : 0 ≤ MP) (hMQ : 0 ≤ MQ)
    (hP : ∀ ij,‖P ij‖ ≤ MP) (hQ : ∀ ij,‖Q ij‖ ≤ MQ)
    (hDual : ∀ ij,∀ f h : SphereSobolev 1,
      ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (P ij f),
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) h)⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) f),
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (Q ij h)⟫_ℝ)
    (hCasimir : ∀ ncut : ℕ,∀ u v : ∀ k,harmonicSphereSubspace k,
      (∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,
        (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*⟪K m n (u n),v m⟫_ℝ)) =
      (1/2:ℝ)*(∑ ij : I × I,(
        ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (P ij (∑ k ∈ Finset.range ncut,sphereSobolevSingleL 1 k (u k))),
          (∑ k ∈ Finset.range ncut,(harmonicSphereRotation k ij.1 ij.2 (v k) : SphereL2))⟫_ℝ-
        ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (P ij (∑ k ∈ Finset.range ncut,sphereSobolevSingleL 1 k (harmonicSphereRotation k ij.1 ij.2 (u k)))),
          (∑ k ∈ Finset.range ncut,(v k : SphereL2))⟫_ℝ))) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ (6*Real.sqrt 2)*(MP+MQ) ∧
      (∀ u,S (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) = T u) ∧
      ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
          ((m:ℝ)-(n:ℝ)) • K m n z := by
  have hM : 0 ≤ (6*Real.sqrt 2)*(MP+MQ) := by positivity
  apply exists_half_degree_extension_of_decoded_form_bound T K hCoeff ((6*Real.sqrt 2)*(MP+MQ)) hM
  intro ncut u v
  have hBound (x y : ∀ k,harmonicSphereSubspace k) :
      |∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,
        (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*⟪K m n (x n),y m⟫_ℝ)| ≤
      (3*Real.sqrt 2*(MP+MQ))*
        Real.sqrt (∑ k ∈ Finset.range ncut,(1+(k:ℝ)*((k:ℝ)+1))*‖x k‖^2)*
        Real.sqrt (∑ k ∈ Finset.range ncut,(1+(k:ℝ)*((k:ℝ)+1))*‖y k‖^2) := by
    rw [hCasimir ncut x y]
    exact finite_physical_casimir_pairing_le_of_adjoint_operator_bounds orthogonalSphereHarmonics denseSphereHarmonics
      P Q MP MQ hMP hMQ hP hQ hDual ncut ncut x y
  have hh := finite_harmonic_degree_half_form_bound_of_casimir_product_bound (Finset.range ncut) K
    (3*Real.sqrt 2*(MP+MQ)) (by positivity) hBound u v
  exact hh.trans_eq (by ring)

end ShrinkingSpheres
