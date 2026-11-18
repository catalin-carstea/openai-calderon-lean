import Proof.WeakPoissonTaylor
import Proof.WeakEnergyEntryNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Matrix
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeCoefficientWeakFunctionalInverse

/-- Uniform low-endpoint first Poisson variation bound from the shared flat
    inverse and the scalar affine coefficient norm. -/
theorem norm_weakFirstPoissonVariationL_le (c : ℝ) {a1 : X → Mat}
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (C0 P : ℝ) (hC0 : 0 ≤ C0) (hP : 0 ≤ P)
    (hInv0 : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0)
    (hA1 : ∀ x ∈ (ballOpens:Set X),∀ i j,|a1 x i j| ≤ P) :
    ‖weakFirstPoissonVariationL c a1 ha1‖ ≤ C0*(9*P)*‖fixedHarmonicH1LiftL‖ := by
  let j := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  let I0 := nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  let T1 := nativeCoefficientWeakEnergyL a1 0 0 ha1
  have hj : ‖j‖ ≤ 1 := Submodule.norm_subtypeL_le _
  have hInv : ‖I0‖ ≤ C0 := hInv0
  have hT1 : ‖T1‖ ≤ 9*P := (norm_nativeWeakEnergyL_of_entries (a:=a1) ha1 P hP hA1).2
  change ‖-(j.comp (I0.comp (T1.comp fixedHarmonicH1LiftL)))‖ ≤ _
  rw [norm_neg]
  calc
    _ ≤ ‖j‖*(‖I0‖*(‖T1‖*‖fixedHarmonicH1LiftL‖)) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ 1*(C0*((9*P)*‖fixedHarmonicH1LiftL‖)) := by gcongr
    _ = _ := by ring

end ShrinkingSpheres
