import Proof.HalfDegreeHigherLiftJets
import Proof.Archive.SphereSobolevFinitePhysicalHalfDualPackets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma half_degree_commutator_adjoint_half_block
    (R S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hS : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z))=
        ((m:ℝ)-(n:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) m (R (sphereSobolevSingleL (1/2:ℝ) n z)))
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m ((-S.adjoint) (sphereSobolevSingleL (1/2:ℝ) n z))=
      ((m:ℝ)-(n:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) m (R.adjoint (sphereSobolevSingleL (1/2:ℝ) n z)) := by
  apply ext_inner_right ℝ
  intro v
  have hTranspose : ⟪sphereSobolevCoefficientL (-(1/2:ℝ)) n (R (sphereSobolevSingleL (1/2:ℝ) m v)),z⟫_ℝ=
      ⟪sphereSobolevCoefficientL (-(1/2:ℝ)) m (R.adjoint (sphereSobolevSingleL (1/2:ℝ) n z)),v⟫_ℝ := by
    rw [←sphereSobolevDualPairing_single_left_physical,←sphereSobolevDualPairing_single_left_physical]
    change ⟪sphereSobolevSingleL (1/2:ℝ) n z,R (sphereSobolevSingleL (1/2:ℝ) m v)⟫_ℝ=
      ⟪sphereSobolevSingleL (1/2:ℝ) m v,R.adjoint (sphereSobolevSingleL (1/2:ℝ) n z)⟫_ℝ
    exact (R.adjoint_inner_left _ _).symm.trans (real_inner_comm _ _)
  have hSTranspose : ⟪sphereSobolevCoefficientL (-(1/2:ℝ)) n (S (sphereSobolevSingleL (1/2:ℝ) m v)),z⟫_ℝ=
      ⟪sphereSobolevCoefficientL (-(1/2:ℝ)) m (S.adjoint (sphereSobolevSingleL (1/2:ℝ) n z)),v⟫_ℝ := by
    rw [←sphereSobolevDualPairing_single_left_physical,←sphereSobolevDualPairing_single_left_physical]
    change ⟪sphereSobolevSingleL (1/2:ℝ) n z,S (sphereSobolevSingleL (1/2:ℝ) m v)⟫_ℝ=
      ⟪sphereSobolevSingleL (1/2:ℝ) m v,S.adjoint (sphereSobolevSingleL (1/2:ℝ) n z)⟫_ℝ
    exact (S.adjoint_inner_left _ _).symm.trans (real_inner_comm _ _)
  have hSAt := congrArg (fun t : harmonicSphereSubspace n => ⟪t,z⟫_ℝ) (hS n m v)
  rw [real_inner_smul_left] at hSAt
  have hNegSwap (t : ℝ) : -(((n:ℝ)-(m:ℝ))*t)=((m:ℝ)-(n:ℝ))*t := by ring
  simp only [_root_.neg_apply,map_neg,inner_neg_left,real_inner_smul_left]
  calc
    _ = -⟪sphereSobolevCoefficientL (-(1/2:ℝ)) n (S (sphereSobolevSingleL (1/2:ℝ) m v)),z⟫_ℝ := congrArg Neg.neg hSTranspose.symm
    _ = -(((n:ℝ)-(m:ℝ))*⟪sphereSobolevCoefficientL (-(1/2:ℝ)) n (R (sphereSobolevSingleL (1/2:ℝ) m v)),z⟫_ℝ) := congrArg Neg.neg hSAt
    _ = -(((n:ℝ)-(m:ℝ))*⟪sphereSobolevCoefficientL (-(1/2:ℝ)) m (R.adjoint (sphereSobolevSingleL (1/2:ℝ) n z)),v⟫_ℝ) :=
      congrArg (fun t : ℝ => -(((n:ℝ)-(m:ℝ))*t)) hTranspose
    _ = _ := hNegSwap _

def halfDegreeAdjointHigherLift
    (R S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := halfDegreeHigherLift R.adjoint (-S.adjoint)

lemma halfDegreeAdjointHigherLift_inclusion
    (R S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hS : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z))=
        ((m:ℝ)-(n:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) m (R (sphereSobolevSingleL (1/2:ℝ) n z))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (halfDegreeAdjointHigherLift R S)=
      R.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  halfDegreeHigherLift_inclusion _ _ (half_degree_commutator_adjoint_half_block R S hS)

lemma norm_halfDegreeAdjointHigherLift_le
    (R S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    ‖halfDegreeAdjointHigherLift R S‖ ≤ ‖R‖+‖S‖ := by
  simpa only [halfDegreeAdjointHigherLift,norm_neg,ContinuousLinearMap.adjoint.norm_map] using norm_halfDegreeHigherLift_le R.adjoint (-S.adjoint)

lemma contDiffOn_halfDegreeAdjointHigherLift
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Y : Set P}
    (R S : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hR : ContDiffOn ℝ ∞ R Y) (hS : ContDiffOn ℝ ∞ S Y) :
    ContDiffOn ℝ ∞ (fun x => halfDegreeAdjointHigherLift (R x) (S x)) Y := by
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hRa : ContDiffOn ℝ ∞ (fun x => (R x).adjoint) Y := Adj.contDiff.comp_contDiffOn hR
  have hSa : ContDiffOn ℝ ∞ (fun x => -(S x).adjoint) Y := (Adj.contDiff.comp_contDiffOn hS).neg
  exact contDiffOn_const.clm_comp ((hRa.clm_comp contDiffOn_const).add (hSa.clm_comp contDiffOn_const))
end ShrinkingSpheres
