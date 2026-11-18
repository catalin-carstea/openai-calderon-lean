import Proof.ConormalSymmetry
import Proof.Archive.SphereSobolevMidpointExtension
import Proof.Archive.SphereSobolevPairingInclusion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralWeightedGraph

/-- Pairing an arbitrary L2 output through its negative-half inclusion needs
    no additional positive-half regularity of that output. -/
theorem boundary_pairing_coarse (z : SphereSobolev (1/2:ℝ)) (v : SphereSobolev 0) :
    sphereSobolevDualPairing (1/2:ℝ) z
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) v) =
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) z,v⟫_ℝ := by
  rw [sphereSobolevDualPairing_eq_tsum,inner_sphereSobolev 0]
  simp only [sphereSobolevCoefficientL_inclusion,besselWeight_zero_order,one_pow,one_mul]

/-- A midpoint extension compatible with a symmetric weak conormal form is
    symmetric in the physical L2 pairing on its H1 domain. -/
theorem conormal_midpoint_symmetric
    (T0 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hLower : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      T0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hSym : ∀ f g,sphereSobolevDualPairing (1/2:ℝ) g (T0 f) = sphereSobolevDualPairing (1/2:ℝ) f (T0 g))
    (u v : SphereSobolev 1) :
    ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,R v⟫_ℝ := by
  let I1 := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  have hU := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u) hLower
  have hV := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A v) hLower
  have hIU := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u)
    (sphereSobolevInclusionL_trans 1 (1/2:ℝ) 0 (by norm_num) (by norm_num))
  have hIV := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A v)
    (sphereSobolevInclusionL_trans 1 (1/2:ℝ) 0 (by norm_num) (by norm_num))
  have hLeft : sphereSobolevDualPairing (1/2:ℝ) (I1 v) (T0 (I1 u)) = ⟪R u,I0 v⟫_ℝ :=
    (congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) (I1 v) z) hU.symm).trans
      ((boundary_pairing_coarse (I1 v) (R u)).trans
        ((congrArg (fun z : SphereSobolev 0 => ⟪z,R u⟫_ℝ) hIV).trans (real_inner_comm _ _)))
  have hRight : sphereSobolevDualPairing (1/2:ℝ) (I1 u) (T0 (I1 v)) = ⟪I0 u,R v⟫_ℝ :=
    (congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) (I1 u) z) hV.symm).trans
      ((boundary_pairing_coarse (I1 u) (R v)).trans (congrArg (fun z : SphereSobolev 0 => ⟪z,R v⟫_ℝ) hIU))
  exact hLeft.symm.trans ((hSym (I1 u) (I1 v)).trans hRight)

end ShrinkingSpheres
