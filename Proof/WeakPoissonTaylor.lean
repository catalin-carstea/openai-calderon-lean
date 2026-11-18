import Proof.NativeWeakTaylorOperators
import Proof.WeakEnergyAffineTaylor
import Proof.WeakPoissonComparison
import Proof.PoissonFirstVariationBound
import Proof.WeakEnergyAffineCross
import Proof.UniformWeakConormalComparison
import Proof.WeakEnergyEntryNorm
import Proof.CanonicalWeakPoissonAssembly
import Proof.CanonicalWeakInvertibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Matrix
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeCoefficientWeakFunctionalInverse nativeCoefficientWeakEnergyL
  OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion

def weakFirstPoissonVariationL (c : ℝ) (a1 : X → Mat)
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  -((TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL.comp
    ((nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)).comp
      ((nativeCoefficientWeakEnergyL a1 0 0 ha1).comp fixedHarmonicH1LiftL)))

/-- The actual weak Poisson lift has a quadratic affine Taylor remainder,
    controlled by local coefficient entries and the shared actual inverses. -/
theorem norm_nativeWeakHalfLift_first_remainder_le {a a1 : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (c r C C0 D P Q : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hc0 : IsCoercive (TauCeti.PDE.energyFormH1L0 (flatCoefficientBound c)))
    (hInv : ‖nativeCoefficientWeakFunctionalInverse a 0 0 ha‖ ≤ C)
    (hInv0 : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0)
    (hDiff : ∀ x ∈ (ballOpens : Set X),∀ i j,|a x i j-(c • (1:Mat)) i j| ≤ D*r)
    (hA1 : ∀ x ∈ (ballOpens : Set X),∀ i j,|a1 x i j| ≤ P)
    (hTaylor : ∀ x ∈ (ballOpens : Set X),∀ i j,|(a x-c • (1:Mat)-r • a1 x) i j| ≤ Q*r^2) :
    ‖nativeWeakHalfLift a 0 0 ha sphereFischerInner-fixedHarmonicH1LiftL-r • weakFirstPoissonVariationL c a1 ha1‖ ≤
      C*(9*Q+C0*(9*D)*(9*P))*‖fixedHarmonicH1LiftL‖*r^2 := by
  let j : BallH1Zero →L[ℝ] BallH1 := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  let A := nativeZeroCoefficientEnergyL a 0 0 ha
  let A0 := nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  let T := nativeCoefficientWeakEnergyL a 0 0 ha
  let T0 := nativeCoefficientWeakEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  let T1 := nativeCoefficientWeakEnergyL a1 0 0 ha1
  have hj : ‖j‖ ≤ 1 := Submodule.norm_subtypeL_le _
  have hA := nativeZeroCoefficientEnergy_isInvertible (a:=a) ha hc
  have hA0 := nativeZeroCoefficientEnergy_isInvertible (a:=fun _ : X => c • (1:Mat)) (flatCoefficientBound c) hc0
  have hInvA : ‖A.inverse‖ ≤ C := by
    dsimp only [A]
    rw [nativeZeroCoefficientEnergy_inverse_eq (a:=a) ha]
    exact hInv
  have hInvA0 : ‖A0.inverse‖ ≤ C0 := by
    dsimp only [A0]
    rw [nativeZeroCoefficientEnergy_inverse_eq]
    exact hInv0
  have hADiff : ‖A-A0‖ ≤ (9*D)*r :=
    (norm_nativeZeroCoefficientEnergy_sub_le (a:=a) (a0:=fun _ : X => c • (1:Mat))
      ha (flatCoefficientBound c) (D*r) (mul_nonneg hD hr) hDiff).trans_eq (by ring)
  have hT1 : ‖T1‖ ≤ 9*P := (norm_nativeWeakEnergyL_of_entries (a:=a1) ha1 P hP hA1).2
  have hTError : ‖T-T0-r • T1‖ ≤ (9*Q)*r^2 :=
    (norm_nativeWeakEnergy_affine_remainder_le (a:=a) (a0:=fun _ : X => c • (1:Mat)) (a1:=a1)
      ha (flatCoefficientBound c) ha1 r (Q*r^2) (mul_nonneg hQ (sq_nonneg _)) hTaylor).trans_eq (by ring)
  have hFlat : T0.comp fixedHarmonicH1LiftL = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousLinearMap.ext
    intro v
    change T0 (fixedHarmonicH1LiftL f) v = 0
    dsimp only [T0]
    rw [nativeCoefficientWeakEnergyL_apply]
    exact fixedHarmonicH1Lift_flat_weak c f v
  have hLiftEq : nativeWeakHalfLift a 0 0 ha sphereFischerInner =
      fixedHarmonicH1LiftL-j.comp (A.inverse.comp (T.comp fixedHarmonicH1LiftL)) := by
    have hI : A.inverse = nativeCoefficientWeakFunctionalInverse a 0 0 ha :=
      nativeZeroCoefficientEnergy_inverse_eq ha
    have hChange := congrArg (fun I0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero =>
      fixedHarmonicH1LiftL-j.comp (I0.comp (T.comp fixedHarmonicH1LiftL))) hI.symm
    exact (nativeWeakHalfLift_native_assembly (a:=a) ha).trans hChange
  have hb := norm_poisson_first_variation_remainder_le j A A0 T T0 T1 fixedHarmonicH1LiftL hA hA0 hFlat hj
    r C C0 (9*D) (9*P) (9*Q) hr hC hC0 (by positivity) (by positivity) (by positivity)
      hInvA hInvA0 hADiff hT1 hTError
  have hInv0Eq : A0.inverse =
      nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c) :=
    nativeZeroCoefficientEnergy_inverse_eq _
  have hFirstEq : -(j.comp (A0.inverse.comp (T1.comp fixedHarmonicH1LiftL))) =
      weakFirstPoissonVariationL c a1 ha1 :=
    congrArg (fun I0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero =>
      -(j.comp (I0.comp (T1.comp fixedHarmonicH1LiftL)))) hInv0Eq
  have hResultEq := congrArg₂ (fun Pa P1 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 =>
    Pa-fixedHarmonicH1LiftL-r • P1) hLiftEq.symm hFirstEq
  have hNorm := congrArg (fun S : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 => ‖S‖) hResultEq
  exact hNorm ▸ hb

end ShrinkingSpheres
