import Proof.HarmonicRotationLieAlgebra
import Proof.RotationDistributionFromBlocks
import Proof.CoarseAngularProductPackets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

def rotationLieCoarseL (i j a b : I) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (if j=a then sphereSobolevRotationL 1 i b else 0)-
    (if j=b then sphereSobolevRotationL 1 i a else 0)-
    (if i=a then sphereSobolevRotationL 1 j b else 0)+
    (if i=b then sphereSobolevRotationL 1 j a else 0)

lemma coarsePhysicalHarmonicBlock_add_apply
    (A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (m n : ℕ) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock (A+B) m n z = coarsePhysicalHarmonicBlock A m n z+coarsePhysicalHarmonicBlock B m n z := by
  simp only [coarsePhysicalHarmonicBlock,ContinuousLinearMap.comp_apply,_root_.add_apply,map_add]
lemma coarsePhysicalHarmonicBlock_sub_apply
    (A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (m n : ℕ) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock (A-B) m n z = coarsePhysicalHarmonicBlock A m n z-coarsePhysicalHarmonicBlock B m n z := by
  simp only [coarsePhysicalHarmonicBlock,ContinuousLinearMap.comp_apply,_root_.sub_apply,map_sub]
lemma coarsePhysicalHarmonicBlock_zero_apply (m n : ℕ) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock 0 m n z = 0 := by
  simp only [coarsePhysicalHarmonicBlock,ContinuousLinearMap.comp_apply,_root_.zero_apply,map_zero]
lemma coarsePhysicalHarmonicBlock_ite_apply (P : Prop) [Decidable P]
    (A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (m n : ℕ) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock (if P then A else B) m n z =
      if P then coarsePhysicalHarmonicBlock A m n z else coarsePhysicalHarmonicBlock B m n z := by
  split_ifs <;> rfl

lemma coarsePhysicalHarmonicBlock_rotation_self (a b : I) (n : ℕ) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock (sphereSobolevRotationL 1 a b) n n z = harmonicSphereRotation n a b z := by
  change sphereSobolevCoefficientL 0 n (sphereSobolevRotationL 1 a b (sphereSobolevSingleL 1 n z)) = _
  rw [orderOneRotation_coefficient,sphereSobolevCoefficientL_single_self]
lemma coarsePhysicalHarmonicBlock_rotation_ne (a b : I) (m n : ℕ) (hmn : m ≠ n) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock (sphereSobolevRotationL 1 a b) m n z = 0 := by
  change sphereSobolevCoefficientL 0 m (sphereSobolevRotationL 1 a b (sphereSobolevSingleL 1 n z)) = _
  rw [orderOneRotation_coefficient,sphereSobolevCoefficientL_single_ne _ _ _ hmn,map_zero]

lemma coarsePhysicalHarmonicBlock_rotationLie_self (i j a b : I) (n : ℕ) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock (rotationLieCoarseL i j a b) n n z =
      (if j=a then harmonicSphereRotation n i b z else 0)-
      (if j=b then harmonicSphereRotation n i a z else 0)-
      (if i=a then harmonicSphereRotation n j b z else 0)+
      (if i=b then harmonicSphereRotation n j a z else 0) := by
  simp only [rotationLieCoarseL,coarsePhysicalHarmonicBlock_add_apply,coarsePhysicalHarmonicBlock_sub_apply,
    coarsePhysicalHarmonicBlock_ite_apply,coarsePhysicalHarmonicBlock_zero_apply,coarsePhysicalHarmonicBlock_rotation_self]
lemma coarsePhysicalHarmonicBlock_rotationLie_ne (i j a b : I) (m n : ℕ) (hmn : m ≠ n) (z : harmonicSphereSubspace n) :
    coarsePhysicalHarmonicBlock (rotationLieCoarseL i j a b) m n z = 0 := by
  simp only [rotationLieCoarseL,coarsePhysicalHarmonicBlock_add_apply,coarsePhysicalHarmonicBlock_sub_apply,
    coarsePhysicalHarmonicBlock_ite_apply,coarsePhysicalHarmonicBlock_zero_apply,
    coarsePhysicalHarmonicBlock_rotation_ne i b m n hmn,
    coarsePhysicalHarmonicBlock_rotation_ne i a m n hmn,
    coarsePhysicalHarmonicBlock_rotation_ne j b m n hmn,
    coarsePhysicalHarmonicBlock_rotation_ne j a m n hmn,ite_self,sub_self,add_zero]

lemma rotationLie_coarse_distribution (i j a b : I) (f : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (sphereSobolevRotationL 1 a b (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (rotationLieCoarseL i j a b (sphereSobolevInclusionL 2 1 (by norm_num) f)+
          sphereSobolevRotationL 1 a b (sphereSobolevRotationL 2 i j f)) := by
  apply rotation_distribution_of_physical_blocks i j (sphereSobolevRotationL 1 a b) (rotationLieCoarseL i j a b)
  intro m n z
  by_cases hmn : m=n
  · subst m
    rw [coarsePhysicalHarmonicBlock_rotationLie_self,coarsePhysicalHarmonicBlock_rotation_self,
      coarsePhysicalHarmonicBlock_rotation_self]
    exact (OAI.AnisotropicCalderon.RotationLieAlgebra.harmonicSphereRotation_lie_commutator n i j a b z).symm
  · simp only [coarsePhysicalHarmonicBlock_rotationLie_ne i j a b m n hmn,
      coarsePhysicalHarmonicBlock_rotation_ne a b m n hmn,map_zero,sub_self]

lemma rotationLieCoarseL_skew (i j a b : I) (u v : SphereSobolev 1) :
    ⟪rotationLieCoarseL i j a b u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,-rotationLieCoarseL i j a b v⟫_ℝ := by
  unfold rotationLieCoarseL
  split_ifs <;> simp only [_root_.sub_apply,_root_.add_apply,_root_.zero_apply,
    inner_sub_left,inner_add_left,inner_neg_right,inner_zero_left,inner_zero_right,
    orderOneRotation_skew,inner_sub_right,inner_add_right] <;> ring

/-- The genuine rotation generators supply a complete bounded angular
    packet through the supplied harmonic Lie identity. -/
def rotationCoarseAdjointPacket (a b : I) : CoarseRotationAdjointPacket where
  operator := sphereSobolevRotationL 1 a b
  adjoint := -sphereSobolevRotationL 1 a b
  angular ij := rotationLieCoarseL ij.1 ij.2 a b
  angularAdjoint ij := -rotationLieCoarseL ij.1 ij.2 a b
  pairing u v := (orderOneRotation_skew u v a b).trans (inner_neg_right _ _).symm
  graph ij := rotationLie_coarse_distribution ij.1 ij.2 a b
  angularPairing ij := rotationLieCoarseL_skew ij.1 ij.2 a b

end ShrinkingSpheres
