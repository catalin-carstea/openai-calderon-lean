import Proof.WeakConormalTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativePolynomialBulkMoments
attribute [local irreducible] weakFirstPoissonVariationL

/-- A common weak first Poisson bound gives a common first conormal bound. -/
theorem norm_weakFirstConormalVariationL_le (c : ℝ) {a1 : X → Mat}
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (K P CP1 : ℝ) (hK : 0 ≤ K) (hP : 0 ≤ P) (hCP1 : 0 ≤ CP1)
    (hE0 : ‖TauCeti.PDE.energyFormH1L (flatCoefficientBound c)‖ ≤ K)
    (hE1 : ‖TauCeti.PDE.energyFormH1L ha1‖ ≤ 9*P)
    (hP1 : ‖weakFirstPoissonVariationL c a1 ha1‖ ≤ CP1) :
    ‖weakFirstConormalVariationL c a1 ha1‖ ≤
      sphereSurfaceMass⁻¹*((K*CP1+9*P*‖fixedHarmonicH1LiftL‖)*‖fixedHarmonicH1LiftL‖) := by
  let E0 := TauCeti.PDE.energyFormH1L (flatCoefficientBound c)
  let E1 := TauCeti.PDE.energyFormH1L ha1
  let P0 := fixedHarmonicH1LiftL
  let P1 := weakFirstPoissonVariationL c a1 ha1
  let B := E0.bilinearComp P1 P0+E1.bilinearComp P0 P0
  let C := (K*CP1+9*P*‖P0‖)*‖P0‖
  have hC : 0 ≤ C := by
    change 0 ≤ (K*CP1+9*P*‖P0‖)*‖P0‖
    exact mul_nonneg (add_nonneg (mul_nonneg hK hCP1)
      (mul_nonneg (mul_nonneg (by norm_num) hP) (norm_nonneg _))) (norm_nonneg _)
  have hB : ‖B‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ hC
    intro f z
    change ‖E0 (P1 f) (P0 z)+E1 (P0 f) (P0 z)‖ ≤ _
    calc
      _ ≤ ‖E0 (P1 f) (P0 z)‖+‖E1 (P0 f) (P0 z)‖ := norm_add_le _ _
      _ ≤ ‖E0‖*(‖P1‖*‖f‖)*(‖P0‖*‖z‖)+‖E1‖*(‖P0‖*‖f‖)*(‖P0‖*‖z‖) := by
        exact add_le_add ((E0.le_opNorm₂ _ _).trans (by gcongr;exact P1.le_opNorm f;exact P0.le_opNorm z))
          ((E1.le_opNorm₂ _ _).trans (by gcongr;exact P0.le_opNorm f;exact P0.le_opNorm z))
      _ ≤ K*(CP1*‖f‖)*(‖P0‖*‖z‖)+(9*P)*(‖P0‖*‖f‖)*(‖P0‖*‖z‖) := by gcongr
      _ = _ := by dsimp [C];ring
  have hRiesz : ‖sphereSobolevDualRieszL (1/2:ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ell
    rw [norm_sphereSobolevDualRieszL_apply,one_mul]
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hScale := norm_nonneg_smul_bilinear_le sphereSurfaceMass⁻¹ hArea B C hB
  change ‖(sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ • B)‖ ≤ sphereSurfaceMass⁻¹*C
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hRiesz hScale (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

end ShrinkingSpheres
