import Proof.CoarseHalfDualCompletion
import Proof.PhysicalHarmonicBlockCasimir
import Proof.Archive.SphereSobolevShiftedPhysicalDegree

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.RotationCasimirEstimate
open OAI.AnisotropicCalderon.SpectralSylvester
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

/-- The distributional degree commutator defined using only a coarse
    first-order operator. -/
def coarseDegreeCommutator (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    SphereSobolev 2 →L[ℝ] SphereSobolev (-1:ℝ) :=
  (sphereSobolevShiftedDegreeL 0).comp
    (R.comp (sphereSobolevInclusionL 2 1 (by norm_num)))-
  (sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num)).comp
    (R.comp (sphereSobolevShiftedDegreeL 2))

lemma coarseDegreeCommutator_physical_block
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-1:ℝ) m
      (coarseDegreeCommutator R (sphereSobolevSingleL 2 n z)) =
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock R m n z := by
  have hD (f : SphereSobolev 0) :
      sphereSobolevCoefficientL (-1:ℝ) m (sphereSobolevShiftedDegreeL 0 f) =
        (m:ℝ) • sphereSobolevCoefficientL 0 m f := by
    simpa only [sphereSobolevCoefficientL,show (0:ℝ)-1=-1 by norm_num] using
      sphereSobolevCoefficientL_shiftedDegree 0 m f
  have hS : sphereSobolevShiftedDegreeL 2 (sphereSobolevSingleL 2 n z) =
      (n:ℝ) • sphereSobolevSingleL 1 n z := by
    simpa only [sphereSobolevSingleL,show (2:ℝ)-1=1 by norm_num] using
      sphereSobolevShiftedDegreeL_single 2 n z
  change sphereSobolevCoefficientL (-1:ℝ) m
    (sphereSobolevShiftedDegreeL 0
      (R (sphereSobolevInclusionL 2 1 (by norm_num) (sphereSobolevSingleL 2 n z)))-
     sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num)
      (R (sphereSobolevShiftedDegreeL 2 (sphereSobolevSingleL 2 n z)))) = _
  rw [map_sub,hD,sphereSobolevInclusionL_single,hS,map_smul,
    sphereSobolevCoefficientL_inclusion,map_smul]
  exact (sub_smul (m:ℝ) (n:ℝ) (coarsePhysicalHarmonicBlock R m n z)).symm

/-- Rotation graphs and true adjoints suffice to construct the half-order
    degree commutator of any coarse first-order operator. -/
theorem exists_half_degree_commutator_of_coarse_rotation_blocks
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (P Q : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (MP MQ : ℝ) (hMP : 0 ≤ MP) (hMQ : 0 ≤ MQ)
    (hP : ∀ ij,‖P ij‖ ≤ MP) (hQ : ∀ ij,‖Q ij‖ ≤ MQ)
    (hDual : ∀ ij,∀ u v : SphereSobolev 1,
      ⟪P ij u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Q ij v⟫_ℝ)
    (hGraph : ∀ ij : I × I,∀ m n : ℕ,∀ z,
      coarsePhysicalHarmonicBlock (P ij) m n z =
        harmonicSphereRotation m ij.1 ij.2 (coarsePhysicalHarmonicBlock R m n z)-
          coarsePhysicalHarmonicBlock R m n (harmonicSphereRotation n ij.1 ij.2 z)) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ (6*Real.sqrt 2)*(MP+MQ) ∧
      (∀ u v,sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
        (S (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)) =
          sphereSobolevDualPairing 1 v (coarseDegreeCommutator R u)) ∧
      ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
          ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock R m n z := by
  let K := coarsePhysicalHarmonicBlock R
  let M := (6*Real.sqrt 2)*(MP+MQ)
  have hM : 0 ≤ M := by positivity
  have hPhysical : ∀ ij,∀ f h : SphereSobolev 1,
      ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (P ij f),
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) h)⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (sphereSobolevInclusionL 1 0 (by norm_num) f),
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (Q ij h)⟫_ℝ := by
    intro ij f h
    rw [(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.inner_map_map,
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.inner_map_map]
    exact hDual ij f h
  have hBound (ncut : ℕ) (u v : ∀ k,harmonicSphereSubspace k) :
      |∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,
        ((m:ℝ)-(n:ℝ))*⟪K m n (u n),v m⟫_ℝ| ≤
      M*Real.sqrt (∑ k ∈ Finset.range ncut,(1+(k:ℝ))*‖u k‖^2)*
        Real.sqrt (∑ k ∈ Finset.range ncut,(1+(k:ℝ))*‖v k‖^2) := by
    have hCasimir (x y : ∀ k,harmonicSphereSubspace k) :
      |∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,
        (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*⟪K m n (x n),y m⟫_ℝ)| ≤
      (3*Real.sqrt 2*(MP+MQ))*
        Real.sqrt (∑ k ∈ Finset.range ncut,(1+(k:ℝ)*((k:ℝ)+1))*‖x k‖^2)*
        Real.sqrt (∑ k ∈ Finset.range ncut,(1+(k:ℝ)*((k:ℝ)+1))*‖y k‖^2) := by
      rw [finite_physical_casimir_of_rotation_blocks K P hGraph]
      exact finite_physical_casimir_pairing_le_of_adjoint_operator_bounds
        orthogonalSphereHarmonics denseSphereHarmonics P Q MP MQ hMP hMQ hP hQ hPhysical ncut ncut x y
    have hh := finite_harmonic_degree_half_form_bound_of_casimir_product_bound (Finset.range ncut) K
      (3*Real.sqrt 2*(MP+MQ)) (by positivity) hCasimir u v
    exact hh.trans_eq (by dsimp only [M];ring)
  obtain ⟨S,hS,hPair,hCoeff⟩ := exists_half_operator_of_finite_coarse_dual_pairs
    (coarseDegreeCommutator R) M hM
    (finite_coarse_dual_degree_pair_bound_of_decoded_form_bound (coarseDegreeCommutator R)
      K (coarseDegreeCommutator_physical_block R) M hM hBound)
  refine ⟨S,hS,hPair,?_⟩
  intro m n z
  exact (hCoeff m n z).trans (coarseDegreeCommutator_physical_block R m n z)

end ShrinkingSpheres
