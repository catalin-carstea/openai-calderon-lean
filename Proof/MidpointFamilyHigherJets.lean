import Proof.MidpointFamilyDerivativeBound
import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Genuine endpoint compatibility is inherited by every finite parameter
    derivative of the same actual families, before interpolation. -/
theorem clm_compatible_endpoint_iteratedFDerivatives
    {P A B C D : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup D] [NormedSpace ℝ D]
    (L : P → B →L[ℝ] D) (H : P → A →L[ℝ] C)
    (J : C →L[ℝ] D) (K : A →L[ℝ] B) (x : P)
    (hL : ContDiffAt ℝ ∞ L x) (hH : ContDiffAt ℝ ∞ H x)
    (hCompatible : (fun p => J.comp (H p)) =ᶠ[𝓝 x] fun p => (L p).comp K)
    (n : ℕ) (v : Fin n → P) :
    J.comp (iteratedFDeriv ℝ n H x v) = (iteratedFDeriv ℝ n L x v).comp K := by
  let Post : (A →L[ℝ] C) →L[ℝ] (A →L[ℝ] D) := ContinuousLinearMap.compL ℝ A C D J
  let Pre : (B →L[ℝ] D) →L[ℝ] (A →L[ℝ] D) := (ContinuousLinearMap.compL ℝ A B D).flip K
  have hLeft := Post.iteratedFDeriv_comp_left hH (i:=n) (by simp)
  have hRight := Pre.iteratedFDeriv_comp_left hL (i:=n) (by simp)
  have hSame := hLeft.symm.trans (((hCompatible.iteratedFDeriv ℝ n).eq_of_nhds).trans hRight)
  exact congrArg (fun A => A v) hSame

open OAI.AnisotropicCalderon.SphereHarmonic

/-- True low/high Taylor jet bounds interpolate to the same actual H1-to-L2
    midpoint family at every finite parameter order. -/
theorem norm_iteratedFDeriv_midpoint_family_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-1/2:ℝ))
    (H : P → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (R : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (x : P)
    (hL : ContDiffAt ℝ ∞ L x) (hH : ContDiffAt ℝ ∞ H x) (hR : ContDiffAt ℝ ∞ R x)
    (hLH : (fun p => (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp (H p)) =ᶠ[𝓝 x]
      fun p => (L p).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hRH : (fun p => (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H p)) =ᶠ[𝓝 x]
      fun p => (R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (n : ℕ) (CL CH : ℝ) (hCL : 0 ≤ CL) (hCH : 0 ≤ CH)
    (hNL : ‖iteratedFDeriv ℝ n L x‖ ≤ CL) (hNH : ‖iteratedFDeriv ℝ n H x‖ ≤ CH) :
    ‖iteratedFDeriv ℝ n R x‖ ≤ (CL+CH)/2 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hDLow := clm_compatible_endpoint_iteratedFDerivatives L H
    (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) x hL hH hLH n v
  have hDMid := clm_compatible_endpoint_iteratedFDerivatives R H
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) x hR hH hRH n v
  let C := sphereSobolevMidpointL (iteratedFDeriv ℝ n L x v) (iteratedFDeriv ℝ n H x v) hDLow
  have hC := sphereSobolevMidpointL_inclusion (iteratedFDeriv ℝ n L x v) (iteratedFDeriv ℝ n H x v) hDLow
  have hEqComp := hDMid.symm.trans hC.symm
  have hEq : iteratedFDeriv ℝ n R x v = C := by
    apply DFunLike.ext'
    exact (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer
      (iteratedFDeriv ℝ n R x v).continuous C.continuous
      (funext fun f => congrArg (fun T => T f) hEqComp)
  have hLo : ‖iteratedFDeriv ℝ n L x v‖ ≤ CL*∏ j,‖v j‖ :=
    ((iteratedFDeriv ℝ n L x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hNL (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  have hHi : ‖iteratedFDeriv ℝ n H x v‖ ≤ CH*∏ j,‖v j‖ :=
    ((iteratedFDeriv ℝ n H x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hNH (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  rw [hEq]
  exact (norm_sphereSobolevMidpointL_le _ _ hDLow).trans (by
    have hSum := add_le_add hLo hHi
    nlinarith only [hSum])

end ShrinkingSpheres
