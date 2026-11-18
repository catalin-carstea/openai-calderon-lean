import Proof.PhysicalPotentialCoreAdjunction
import Proof.Archive.NativeHarmonicHalfCoarseDualPairing
import Proof.Archive.SphereSobolevFinitePhysicalHalfDualPackets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

lemma potentialQuadraticCoreL_coefficient (P : PhysicalPrincipalData Y d CF CT) {y : X}
    (hy : y ∈ Y) {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (5/2:ℝ)) (k : ℕ) :
    sphereSobolevCoefficientL 0 k (P.potentialQuadraticCoreL W u)=
      sphereSobolevCoefficientL (-(1/2:ℝ)) k
        (P.potentialQuadraticHalfL y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)) := by
  have h := congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) k) (P.potentialQuadraticCoreL_balanced hy W u)
  simpa only [sphereSobolevCoefficientL_inclusion] using h

/-- The true physical adjunction determines every reverse-output harmonic
coefficient directly from the smooth balanced potential. It requires no
smoothness assumption on a pointwise selected higher witness. -/
lemma potentialQuadraticAdjointCoreL_coefficient (P : PhysicalPrincipalData Y d CF CT) {y : X}
    (hy : y ∈ Y) {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (5/2:ℝ)) (k : ℕ) :
    sphereSobolevCoefficientL 0 k (P.potentialQuadraticAdjointCoreL W u)=
      ((P.potentialQuadraticHalfL y).comp (sphereSobolevSingleL (3/2:ℝ) k)).adjoint
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) u) := by
  apply ext_inner_right ℝ
  intro z
  let A := P.potentialQuadraticCoreL W
  let B := P.potentialQuadraticAdjointCoreL W
  let T := (P.potentialQuadraticHalfL y).comp (sphereSobolevSingleL (3/2:ℝ) k)
  let uH := sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) u
  have hSingle : ⟪sphereSobolevCoefficientL 0 k (B u),z⟫_ℝ=
      ⟪sphereSobolevSingleL 0 k z,B u⟫_ℝ :=
    by
      have h := sphereSobolevDualPairing_single_left_physical 0 k z (B u)
      have hC : sphereSobolevCoefficientL (-(0:ℝ)) k=sphereSobolevCoefficientL 0 k := by congr 1 <;> norm_num
      rw [hC] at h
      exact h.symm
  have hAdj := P.potentialQuadraticCoreL_pair hy W (sphereSobolevSingleL (5/2:ℝ) k z) u
  rw [sphereSobolevInclusionL_single] at hAdj
  have hGraph := P.potentialQuadraticCoreL_balanced hy W (sphereSobolevSingleL (5/2:ℝ) k z)
  rw [sphereSobolevInclusionL_single] at hGraph
  have hPair := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) uH
    (A (sphereSobolevSingleL (5/2:ℝ) k z))
  dsimp only [uH] at hPair
  rw [sphereSobolevInclusionL_trans_apply] at hPair
  calc
    _ = ⟪sphereSobolevSingleL 0 k z,B u⟫_ℝ := hSingle
    _ = ⟪A (sphereSobolevSingleL (5/2:ℝ) k z),sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) u⟫_ℝ := hAdj.symm
    _ = ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) u,A (sphereSobolevSingleL (5/2:ℝ) k z)⟫_ℝ := real_inner_comm _ _
    _ = sphereSobolevDualPairing (1/2:ℝ) uH
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (A (sphereSobolevSingleL (5/2:ℝ) k z))) := hPair.symm
    _ = ⟪uH,T z⟫_ℝ := congrArg (sphereSobolevDualPairing (1/2:ℝ) uH) hGraph
    _ = ⟪T.adjoint uH,z⟫_ℝ := (ContinuousLinearMap.adjoint_inner_left T z uH).symm
end PhysicalPrincipalData
end ShrinkingSpheres
