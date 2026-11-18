import Proof.RotationCommutatorHighLift
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2300
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection OAI.AnisotropicCalderon.SpectralWeightedGraph

/-- The supplied half→three-half reconstruction, for an order-zero
operator and its SAME order-zero rotation commutators. -/
def zeroOrderRotationHighLiftL
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (D : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  sphereSobolevTraceReconstructionIdentityL.comp
    (C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))+
  ∑ i : I,∑ j : I,(sphereSobolevTraceReconstructionRotationL i j).comp
    (C.comp (sphereSobolevRotationL (3/2:ℝ) i j)+
      (D i j).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))

/-- Only the stored operator-norm formula is reused here. Physical grade
compatibility is established independently below from decoded coefficients. -/
lemma norm_zeroOrderRotationHighLiftL_le
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (D : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
    ‖zeroOrderRotationHighLiftL C D‖ ≤ 19*‖C‖+Real.sqrt 2*∑ i : I,∑ j : I,‖D i j‖ :=
  norm_sphereSobolevRotationCommutatorHighLiftL_le C D

lemma halfRotationWitness_stored
    (z : SphereSobolev (1/2:ℝ)) (v : I → I → SphereSobolev (1/2:ℝ))
    (hGraph : ∀ i j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) (v i j)=
      sphereSobolevRotationL (1/2:ℝ) i j z) :
    ∀ i j n,v i j n=harmonicSphereRotation n i j (z n) := by
  intro i j n
  have hRot : sphereSobolevCoefficientL (-(1/2:ℝ)) n
      (sphereSobolevRotationL (1/2:ℝ) i j z)=
      harmonicSphereRotation n i j (sphereSobolevCoefficientL (1/2:ℝ) n z) := by
    have hIndexMap (s t : ℝ) (hst : s=t) :
        (sphereSobolevCoefficientL s n : SphereSobolev (-(1/2:ℝ)) →L[ℝ] harmonicSphereSubspace n)=
          sphereSobolevCoefficientL t n := by
      cases hst
      rfl
    have hMaps := hIndexMap ((1/2:ℝ)-1) (-(1/2:ℝ)) (by norm_num)
    have hEval := congrArg (fun F : SphereSobolev (-(1/2:ℝ)) →L[ℝ] harmonicSphereSubspace n =>
      F (sphereSobolevRotationL (1/2:ℝ) i j z)) hMaps
    exact hEval.symm.trans (sphereSobolevCoefficientL_rotation (1/2:ℝ) i j n z)
  have hCoeff := congrArg (sphereSobolevCoefficientL (-(1/2:ℝ)) n) (hGraph i j)
  have hDecoded : sphereSobolevCoefficientL (1/2:ℝ) n (v i j)=
      harmonicSphereRotation n i j (sphereSobolevCoefficientL (1/2:ℝ) n z) :=
    (sphereSobolevCoefficientL_inclusion (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (v i j) n).symm.trans
      (hCoeff.trans hRot)
  change besselWeight (-(1/2:ℝ)) n • v i j n=
    harmonicSphereRotation n i j (besselWeight (-(1/2:ℝ)) n • z n) at hDecoded
  rw [map_smul] at hDecoded
  have hCancel := congrArg (fun a : harmonicSphereSubspace n => (besselWeight (-(1/2:ℝ)) n)⁻¹ • a) hDecoded
  simpa only [smul_smul,inv_mul_cancel₀ (besselWeight_pos (-(1/2:ℝ)) n).ne',one_smul] using hCancel

lemma zeroOrderRotationHighLiftL_compatible
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (D : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hWitness : ∀ (u : SphereSobolev (3/2:ℝ)) (i j : I),
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (C (sphereSobolevRotationL (3/2:ℝ) i j u)+
          D i j (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=
      sphereSobolevRotationL (1/2:ℝ) i j
        (C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (zeroOrderRotationHighLiftL C D)=
      C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext (1/2:ℝ)
  intro n
  rw [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion]
  have hStored := halfRotationWitness_stored _ _ (hWitness u)
  simpa only [zeroOrderRotationHighLiftL,_root_.add_apply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply] using sphereSobolevCoefficientL_traceReconstruction _ _ hStored n
end ShrinkingSpheres
