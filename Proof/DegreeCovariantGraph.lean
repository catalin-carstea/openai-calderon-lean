import Proof.FlatRaisingHigherAlgebra
import Proof.ActualCovariantRotationGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

lemma sphereSobolevCoefficientL_physicalDegree (k : ℕ) (u : SphereSobolev 1) :
    sphereSobolevCoefficientL 0 k (sphereSobolevDegreeL u)=
      (k:ℝ) • sphereSobolevCoefficientL 1 k u := by
  have hh := sphereSobolevCoefficientL_shiftedDegree 1 k u
  rw [sphereSobolevShiftedDegreeL_one_eq_degree] at hh
  have hC : sphereSobolevCoefficientL ((1:ℝ)-1) k=sphereSobolevCoefficientL 0 k := by
    rw [show (1:ℝ)-1=0 by norm_num]
  rw [hC] at hh
  exact hh

lemma sphereSobolevCoefficientL_rotation_zero (i j : I) (k : ℕ) (u : SphereSobolev 0) :
    sphereSobolevCoefficientL (-1:ℝ) k (sphereSobolevRotationL 0 i j u)=
      harmonicSphereRotation k i j (sphereSobolevCoefficientL 0 k u) := by
  have hh := sphereSobolevCoefficientL_rotation 0 i j k u
  have hC : sphereSobolevCoefficientL ((0:ℝ)-1) k=sphereSobolevCoefficientL (-1:ℝ) k := by
    rw [show (0:ℝ)-1= -1 by norm_num]
  rw [hC] at hh
  exact hh

lemma sphereSobolevCoefficientL_rotation_two (i j : I) (k : ℕ) (u : SphereSobolev 2) :
    sphereSobolevCoefficientL 1 k (sphereSobolevRotationL 2 i j u)=
      harmonicSphereRotation k i j (sphereSobolevCoefficientL 2 k u) := by
  have hh := sphereSobolevCoefficientL_rotation 2 i j k u
  have hC : sphereSobolevCoefficientL ((2:ℝ)-1) k=sphereSobolevCoefficientL 1 k := by
    rw [show (2:ℝ)-1=1 by norm_num]
  rw [hC] at hh
  exact hh

lemma sphereSobolevDegreeL_coarse_rotation (i j : I) (u : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (sphereSobolevDegreeL (sphereSobolevInclusionL 2 1 (by norm_num) u))=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) (sphereSobolevDegreeL (sphereSobolevRotationL 2 i j u)) := by
  apply sphereSobolev_ext (-1:ℝ)
  intro k
  rw [sphereSobolevCoefficientL_rotation_zero,sphereSobolevCoefficientL_physicalDegree,
    sphereSobolevCoefficientL_inclusion,map_smul,sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_physicalDegree,sphereSobolevCoefficientL_rotation_two]

lemma sphereSobolevDegreeL_covariant_graph (d : Data) (y a : X) :
    CoarseCovariantRotationGraph d y a (fun _ => sphereSobolevDegreeL) 0 := by
  intro u
  simp only [_root_.zero_apply,map_zero,fderiv_const_apply,sphereSobolevDegreeL_coarse_rotation,
    sub_self,smul_zero,Finset.sum_const_zero]
end ShrinkingSpheres
