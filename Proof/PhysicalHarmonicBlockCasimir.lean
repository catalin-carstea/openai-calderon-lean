import Proof.HarmonicBlockCasimirCommutator
import Proof.HalfDegreeCommutatorFromCasimir

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SmoothAngularCasimir

/-- The actual physical harmonic block of a coarse response. -/
def coarsePhysicalHarmonicBlock (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (m n : ℕ) :
    harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m :=
  (sphereSobolevCoefficientL 0 m).comp (T.comp (sphereSobolevSingleL 1 n))

lemma coarsePhysicalHarmonicBlock_inner (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (m n : ℕ) (u : harmonicSphereSubspace n) (v : harmonicSphereSubspace m) :
    ⟪coarsePhysicalHarmonicBlock T m n u,v⟫_ℝ =
      ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (T (sphereSobolevSingleL 1 n u)),(v : SphereL2)⟫_ℝ := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let out := T (sphereSobolevSingleL 1 n u)
  have hCoord := sphereSobolevCoefficientL_zeroEquiv orthogonalSphereHarmonics denseSphereHarmonics m (Z.symm out)
  change sphereSobolevCoefficientL 0 m (Z (Z.symm out)) = _ at hCoord
  rw [Z.apply_symm_apply] at hCoord
  change ⟪sphereSobolevCoefficientL 0 m out,v⟫_ℝ = _
  rw [hCoord]
  exact sphereHarmonicCoordinate_inner orthogonalSphereHarmonics denseSphereHarmonics m (Z.symm out) v

lemma finite_coarsePhysicalHarmonicBlock_pairing
    (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (ncut mcut : ℕ)
    (u v : ∀ k,harmonicSphereSubspace k) :
    (∑ m ∈ Finset.range mcut,∑ n ∈ Finset.range ncut,
      ⟪coarsePhysicalHarmonicBlock T m n (u n),v m⟫_ℝ) =
    ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (T (∑ n ∈ Finset.range ncut,sphereSobolevSingleL 1 n (u n))),
      (∑ m ∈ Finset.range mcut,(v m : SphereL2))⟫_ℝ := by
  symm
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_sum,map_sum,sum_inner]
  exact Finset.sum_congr rfl (fun n _ => (coarsePhysicalHarmonicBlock_inner T m n (u n) (v m)).symm)

/-- Exact finite physical Casimir form from actual same-block rotation graphs. -/
theorem finite_physical_casimir_of_rotation_blocks
    (K : ∀ m n : ℕ,harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (P : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hGraph : ∀ ij : I × I,∀ m n : ℕ,∀ z,
      coarsePhysicalHarmonicBlock (P ij) m n z =
        harmonicSphereRotation m ij.1 ij.2 (K m n z)-K m n (harmonicSphereRotation n ij.1 ij.2 z))
    (ncut : ℕ) (u v : ∀ k,harmonicSphereSubspace k) :
    (∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,
      (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1))*⟪K m n (u n),v m⟫_ℝ)) =
      (1/2:ℝ)*(∑ ij : I × I,(
        ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (P ij (∑ k ∈ Finset.range ncut,sphereSobolevSingleL 1 k (u k))),
          (∑ k ∈ Finset.range ncut,(harmonicSphereRotation k ij.1 ij.2 (v k) : SphereL2))⟫_ℝ-
        ⟪(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (P ij (∑ k ∈ Finset.range ncut,sphereSobolevSingleL 1 k (harmonicSphereRotation k ij.1 ij.2 (u k)))),
          (∑ k ∈ Finset.range ncut,(v k : SphereL2))⟫_ℝ)) := by
  let F := fun m n (ij : I × I) =>
    ⟪coarsePhysicalHarmonicBlock (P ij) m n (u n),harmonicSphereRotation m ij.1 ij.2 (v m)⟫_ℝ-
    ⟪coarsePhysicalHarmonicBlock (P ij) m n (harmonicSphereRotation n ij.1 ij.2 (u n)),v m⟫_ℝ
  have hReorder : (∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,∑ ij : I × I,F m n ij) =
      ∑ ij : I × I,∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,F m n ij := by
    calc
      _ = ∑ m ∈ Finset.range ncut,∑ ij : I × I,∑ n ∈ Finset.range ncut,F m n ij := by
        apply Finset.sum_congr rfl
        intro m _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  calc
    _ = (1/2:ℝ)*(∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,∑ ij : I × I,F m n ij) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      simpa only [Finset.mul_sum,F] using harmonic_block_rotation_casimir_form (K m n)
        (fun ij => coarsePhysicalHarmonicBlock (P ij) m n) (fun ij z => hGraph ij m n z) (u n) (v m)
    _ = (1/2:ℝ)*(∑ ij : I × I,∑ m ∈ Finset.range ncut,∑ n ∈ Finset.range ncut,F m n ij) := congrArg (fun x : ℝ => (1/2:ℝ)*x) hReorder
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ij _
      dsimp only [F]
      simp only [Finset.sum_sub_distrib]
      rw [finite_coarsePhysicalHarmonicBlock_pairing,finite_coarsePhysicalHarmonicBlock_pairing]

/-- Checked consumer: native degree bounds now require only same physical
    rotation graphs and their true adjoints; finite spectral completion is closed. -/
theorem exists_half_degree_commutator_of_rotation_blocks
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
    (hGraph : ∀ ij : I × I,∀ m n : ℕ,∀ z,
      coarsePhysicalHarmonicBlock (P ij) m n z =
        harmonicSphereRotation m ij.1 ij.2 (K m n z)-K m n (harmonicSphereRotation n ij.1 ij.2 z)) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ (6*Real.sqrt 2)*(MP+MQ) ∧
      (∀ u,S (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) = T u) ∧
      ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
          ((m:ℝ)-(n:ℝ)) • K m n z :=
  exists_half_degree_commutator_of_casimir_identity T K hCoeff P Q MP MQ hMP hMQ hP hQ hDual
    (finite_physical_casimir_of_rotation_blocks K P hGraph)

end ShrinkingSpheres
