import Proof.WeakFirstVariationNorm
import Proof.FlatNativeWeakData
import Proof.StrongPoissonTaylor
import Proof.WeakStrongPoissonCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeCoefficientWeakFunctionalInverse

/-- The weak and strong affine first Poisson variations are exactly the same
    solution on their common boundary domain, by the actual native forcing identity. -/
theorem weakFirstPoissonVariation_high_compatible (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : 0 < c)
    (hF0 : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 x = 1)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    weakFirstPoissonVariationL c (coefficientMatrixField 2 F1) ha1
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      TauCeti.Wkp.firstOrder 1 (strongFirstPoissonVariationL F0 F1 c f) := by
  let g := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U := fixedHarmonicLiftL f
  let W := (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse
    (fullCoefficientOperatorL fixedSobolevCalculus 0 F1 U)
  let V : BallH1Zero := ⟨TauCeti.Wkp.firstOrder 1 (W : BallSobolev 2),
    (mem_strongDirichletSubmodule 0 (W:BallSobolev 2)).mp W.property⟩
  let A0 := TauCeti.PDE.energyFormH1L0 (flatCoefficientBound c)
  let ell := nativeCoefficientWeakEnergyL (coefficientMatrixField 2 F1) 0 0 ha1 (fixedHarmonicH1LiftL g)
  have hOrder : TauCeti.Wkp.firstOrder 1 U = fixedHarmonicH1LiftL g :=
    firstOrder_harmonicLiftCompletion sphereFischerInner orthogonalSphereHarmonics f
  have hPoint (x : X) (hx : x ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (c • F0) x = c • (1:Mat) := by
    rw [coefficientMatrixField_smul,hF0 x hx]
  have hRestr := congrArg (fun T => T W) (fullCoefficientOperatorL_comp_subtype fixedSobolevCalculus 0 (c • F0))
  have hSolve : fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0) (W:BallSobolev 2) =
      fullCoefficientOperatorL fixedSobolevCalculus 0 F1 U := hRestr.trans (hInv0.self_apply_inverse _)
  have hAV : A0 V = ell := by
    apply ContinuousLinearMap.ext
    intro v
    have hE0 := fullCoefficientOperator_energy fixedSobolevCalculus 0 (c • F0) (W:BallSobolev 2) v
    have hE1 := fullCoefficientOperator_energy fixedSobolevCalculus 0 F1 U v
    rw [hSolve] at hE0
    have hEnergy := (energyFormH1_congr_coeff_on hPoint
      (TauCeti.Wkp.firstOrder 1 (W:BallSobolev 2)) (v:BallH1)).symm.trans (hE0.symm.trans hE1)
    rw [hOrder] at hEnergy
    change A0 V v = ell v
    rw [TauCeti.PDE.energyFormH1L0_apply,nativeCoefficientWeakEnergyL_apply]
    exact hEnergy
  have e0 := flat_native_weak_energy_data c hc
  have hWeakInv := canonicalWeakEnergy_isInvertible (a:=fun _ : X => c • (1:Mat)) (flatCoefficientBound c) e0.coercive
  have hI : A0.inverse ell = V := by rw [← hAV,hWeakInv.inverse_apply_self]
  have hNativeI : nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c) ell = V := by
    rw [nativeCoefficientWeakFunctionalInverse_eq_inverse]
    exact hI
  change -((TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
      (nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c) ell)) =
    TauCeti.Wkp.firstOrder 1 (-(W:BallSobolev 2))
  rw [hNativeI]
  change -((TauCeti.Wkp.firstOrderL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 1) (W:BallSobolev 2)) =
    (TauCeti.Wkp.firstOrderL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 1) (-(W:BallSobolev 2))
  exact ((TauCeti.Wkp.firstOrderL (mu:=(volume:Measure X)) (Omega:=ballOpens) (p:=2) 1).map_neg _).symm

end ShrinkingSpheres
