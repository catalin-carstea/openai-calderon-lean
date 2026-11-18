import Proof.BilinearPoissonTaylor
import Proof.WeakConormalComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments

/-- Passing a quadratic boundary energy remainder through the fixed dual
    Riesz map preserves its order, with the actual probability-sphere factor. -/
theorem norm_conormal_energy_taylor_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E E0 E1 : H →L[ℝ] H →L[ℝ] ℝ)
    (P P0 P1 : SphereSobolev (1/2:ℝ) →L[ℝ] H)
    (r D L A B C : ℝ) (hr : 0 ≤ r) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hE : ‖E‖ ≤ D) (hE1 : ‖E1‖ ≤ L)
    (hEError : ‖E-E0-r • E1‖ ≤ A*r^2)
    (hPError : ‖P-P0-r • P1‖ ≤ B*r^2)
    (hP1 : ‖P1‖ ≤ C) (hEDiff : ‖E-E0‖ ≤ (L+A)*r) :
    ‖(sphereSobolevDualRieszL (1/2:ℝ)).comp
      (sphereSurfaceMass⁻¹ • (E.bilinearComp P P0-E0.bilinearComp P0 P0-
        r • (E0.bilinearComp P1 P0+E1.bilinearComp P0 P0)))‖ ≤
      sphereSurfaceMass⁻¹*((D*B+(L+A)*C+A*‖P0‖)*‖P0‖)*r^2 := by
  have hRiesz : ‖sphereSobolevDualRieszL (1/2:ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ell
    rw [norm_sphereSobolevDualRieszL_apply,one_mul]
  have hb := norm_bilinear_poisson_taylor_le E E0 E1 P P0 P1 r D L A B C hr hD hL hA hB hC
    hE hE1 hEError hPError hP1 hEDiff
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hs := norm_nonneg_smul_bilinear_le sphereSurfaceMass⁻¹ hArea _ _ hb
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hRiesz hs (norm_nonneg _) zero_le_one).trans_eq (by ring))

end ShrinkingSpheres
