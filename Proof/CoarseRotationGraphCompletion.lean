import Proof.RotationGraphHarmonicBlocks
import Proof.OrderOneMultiplierProduct
import Proof.Archive.SphereSobolevSingleRotationAngleDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

def sphereH2PhysicalPartialLift (n : ℕ) (u : SphereSobolev 1) : SphereSobolev 2 :=
  ∑ k ∈ Finset.range n,sphereSobolevSingleL 2 k (sphereSobolevCoefficientL 1 k u)

lemma sphereH2PhysicalPartialLift_inclusion (n : ℕ) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 2 1 (by norm_num) (sphereH2PhysicalPartialLift n u) =
      sphereSobolevPartialSum 1 n u := by
  simp only [sphereH2PhysicalPartialLift,map_sum,sphereSobolevInclusionL_single,sphereSobolevPartialSum]

lemma sphereH2PhysicalPartialLift_rotation_of_graph (i j : I)
    (u v : SphereSobolev 1)
    (hGraph : sphereSobolevRotationL 1 i j u = sphereSobolevInclusionL 1 0 (by norm_num) v)
    (n : ℕ) :
    sphereSobolevRotationL 2 i j (sphereH2PhysicalPartialLift n u) = sphereSobolevPartialSum 1 n v := by
  have hCoeff (k : ℕ) : harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u) =
      sphereSobolevCoefficientL 1 k v := by
    have hh := congrArg (sphereSobolevCoefficientL 0 k) hGraph
    rw [sphereSobolevCoefficientL_inclusion] at hh
    have hR := sphereSobolevCoefficientL_rotation 1 i j k u
    have hR0 : sphereSobolevCoefficientL 0 k (sphereSobolevRotationL 1 i j u) =
        harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u) := by
      simpa only [sphereSobolevCoefficientL,show (1:ℝ)-1=0 by norm_num] using hR
    exact hR0.symm.trans hh
  simp only [sphereH2PhysicalPartialLift,map_sum,sphereSobolevRotationL_single,sphereSobolevPartialSum]
  apply Finset.sum_congr rfl
  intro k _
  have hs : sphereSobolevSingleL ((2:ℝ)-1) k
      (harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u)) =
      sphereSobolevSingleL 1 k (harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u)) := by
    simp only [sphereSobolevSingleL,show (2:ℝ)-1=1 by norm_num]
  exact hs.trans (congrArg (sphereSobolevSingleL 1 k) (hCoeff k))

/-- A bounded coarse rotation identity extends from H2 inputs to the full
    graph domain of that single rotation in H1, by harmonic truncation. -/
theorem coarse_rotation_distribution_of_H1_graph (i j : I)
    (A C : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hA : ∀ f : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (A (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+A (sphereSobolevRotationL 2 i j f)))
    (u v : SphereSobolev 1)
    (hGraph : sphereSobolevRotationL 1 i j u = sphereSobolevInclusionL 1 0 (by norm_num) v) :
    sphereSobolevRotationL 0 i j (A u) =
      sphereSobolevInclusionL 0 (-1) (by norm_num) (C u+A v) := by
  have hEach (n : ℕ) := hA (sphereH2PhysicalPartialLift n u)
  simp only [sphereH2PhysicalPartialLift_inclusion,
    sphereH2PhysicalPartialLift_rotation_of_graph i j u v hGraph] at hEach
  have hLeft := ((sphereSobolevRotationL 0 i j).continuous.tendsto (A u)).comp
    ((A.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum 1 u))
  have hRight := (sphereSobolevInclusionL 0 (-1) (by norm_num)).continuous.tendsto (C u+A v) |>.comp
    (((C.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum 1 u)).add
      ((A.continuous.tendsto v).comp (tendsto_sphereSobolevPartialSum 1 v)))
  exact tendsto_nhds_unique hLeft (hRight.congr' (Filter.Eventually.of_forall (fun n => (hEach n).symm)))

end ShrinkingSpheres
