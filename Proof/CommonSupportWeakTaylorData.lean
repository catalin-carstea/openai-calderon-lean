import Proof.NativeWeakTaylorData
import Proof.CommonSupportTaylorDerivativeData
import Proof.CommonSupportWeakPoissonRegularity
import Proof.WeakFirstVariationDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse

def commonSupportWeakTaylorDerivativeBudget (CW P Q CP2 DA D1 DQ : ℝ) : ℝ :=
  CW*((weakFullDerivativeBudget*DQ+weakFullDerivativeBudget*DA*5*(9*P)+
    (9*(P+Q))*5*(weakFullDerivativeBudget*D1))*‖fixedHarmonicH1LiftL‖+
    weakFullDerivativeBudget*DA*CP2)

/-- Point Taylor data and the native derivative bounds of the SAME compact
    coefficient families give the quadratic derivative of the actual weak lift.
    The open inverse locus is produced from point coercivity and continuity. -/
theorem commonSupport_weak_taylor_derivative_data
    (a a1 : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r CW CA P Q CP1 CP2 DA D1 DQ L : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hCW : 0 ≤ CW) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hCP2 : 0 ≤ CP2) (hDA : 0 ≤ DA) (hD1 : 0 ≤ D1) (hDQ : 0 ≤ DQ) (hL : 0 ≤ L)
    (F0 : SmoothCoefficientMatrix 2)
    (hNative : CommonSupportNativeDerivativeBounds a ha S hS hz (DA*r*L))
    (hNative1 : CommonSupportNativeDerivativeBounds a1 ha1 S1 hS1 hz1 (D1*L))
    (hTaylor : CommonSupportTaylorDerivativeBounds a a1 ha ha1 S S1 hS hS1 hz hz1 r F0 (DQ*r^2*L))
    (hPoint : NativeWeakTaylorData (fun z => a (0,z)) (fun z => a1 (0,z)) 1 r CW CA P Q CP1 CP2)
    (hEntries : RawAffineCoefficientBounds (fun z => a (0,z)) (fun z => a1 (0,z)) 1 r P Q) :
    ∃ U : Set ℝ,IsOpen U ∧ (0:ℝ) ∈ U ∧
      (∀ t ∈ U,(commonSupportZeroWeakEnergy a ha t).IsInvertible) ∧
      DifferentiableAt ℝ (commonSupportWeakHalfLift a ha) 0 ∧
      DifferentiableAt ℝ (fun t => weakFirstPoissonVariationL 1 (fun z => a1 (t,z))
        (commonSupportEnergyMemLp a1 ha1 t)) 0 ∧
      ‖fderiv ℝ (fun t => weakFirstPoissonVariationL 1 (fun z => a1 (t,z))
        (commonSupportEnergyMemLp a1 ha1 t)) 0‖ ≤
          (5*weakFullDerivativeBudget*D1*‖fixedHarmonicH1LiftL‖)*L ∧
      ‖fderiv ℝ (fun t => commonSupportWeakHalfLift a ha t-fixedHarmonicH1LiftL-
        r • weakFirstPoissonVariationL 1 (fun z => a1 (t,z))
          (commonSupportEnergyMemLp a1 ha1 t)) 0‖ ≤
        commonSupportWeakTaylorDerivativeBudget CW P Q CP2 DA D1 DQ*r^2*L := by
  have hWB := weakFullDerivativeBudget_nonneg
  have hASmooth := contDiff_commonSupportZeroWeakEnergy a ha S hS hz
  have hTDiff := (contDiff_commonSupportWeakEnergy a ha S hS hz).differentiable (by simp) 0
  have hT1Diff := (contDiff_commonSupportWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0
  have hAInv : (commonSupportZeroWeakEnergy a ha 0).IsInvertible :=
    nativeZeroCoefficientEnergy_isInvertible (commonSupportEnergyMemLp a ha 0) hPoint.energy.coercive
  let U := {t : ℝ | (commonSupportZeroWeakEnergy a ha t).IsInvertible}
  have hU : IsOpen U := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hASmooth.continuous
  have h0U : (0:ℝ) ∈ U := hAInv
  have hInv : ∀ t ∈ U,(commonSupportZeroWeakEnergy a ha t).IsInvertible := fun _ h => h
  have hPDiff : DifferentiableAt ℝ (commonSupportWeakHalfLift a ha) 0 :=
    ((contDiffOn_commonSupportWeakHalfLift a ha S hS hz U hInv).contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)
  have hFlat := flat_native_weak_energy_data 1 (by norm_num)
  have hI0 : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)‖ ≤ 5 := by
    change ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat))
      (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) (flatCoefficientBound 1)‖ ≤ 5
    simpa only [inv_one,mul_one] using hFlat.inverse_bound
  have hNI0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).inverse‖ ≤ 5 := by
    rw [nativeZeroCoefficientEnergy_inverse_eq]
    exact hI0
  have hInv0 := nativeZeroCoefficientEnergy_isInvertible (flatCoefficientBound 1) hFlat.coercive
  have hNI : ‖(commonSupportZeroWeakEnergy a ha 0).inverse‖ ≤ CW := by
    change ‖(nativeZeroCoefficientEnergyL (fun z => a (0,z)) 0 0 (commonSupportEnergyMemLp a ha 0)).inverse‖ ≤ CW
    rw [nativeZeroCoefficientEnergy_inverse_eq]
    exact hPoint.energy.inverse_bound
  have hNB : ‖commonSupportZeroWeakEnergy a ha 0-
      nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)‖ ≤ (9*(P+Q))*r :=
    (norm_nativeZeroCoefficientEnergy_sub_le (commonSupportEnergyMemLp a ha 0) (flatCoefficientBound 1)
      ((P+Q)*r) (by positivity) hEntries.difference).trans_eq (by ring)
  have hNV1 : ‖commonSupportWeakEnergy a1 ha1 0‖ ≤ 9*P :=
    (norm_nativeWeakEnergyL_of_entries (commonSupportEnergyMemLp a1 ha1 0) P hP hEntries.first).2
  have hNA : ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) 0‖ ≤ (weakFullDerivativeBudget*DA*L)*r :=
    hNative.zeroWeak.trans_eq (by ring)
  have hND1 : ‖fderiv ℝ (commonSupportWeakEnergy a1 ha1) 0‖ ≤ weakFullDerivativeBudget*D1*L :=
    hNative1.weak.trans_eq (by ring)
  have hNDQ : ‖fderiv ℝ (fun t => commonSupportWeakEnergy a ha t-
      nativeCoefficientWeakEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
      r • commonSupportWeakEnergy a1 ha1 t) 0‖ ≤ (weakFullDerivativeBudget*DQ*L)*r^2 :=
    hTaylor.weak.trans_eq (by ring)
  obtain ⟨hP1Diff,hDP1⟩ := commonSupport_weakFirstPoisson_derivative a1 ha1 1 0 hT1Diff
    5 (weakFullDerivativeBudget*D1*L) (by norm_num) (by positivity) hI0 hND1
  have hBulkPoint : ‖commonSupportWeakHalfLift a ha 0-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL 1 (fun z => a1 (0,z)) (commonSupportEnergyMemLp a1 ha1 0)‖ ≤ CP2*r^2 :=
    hPoint.poisson_remainder_bound
  have hBound := norm_nativeWeakHalfLift_first_remainder_derivative_le
    (fun t z => a (t,z)) (fun t z => a1 (t,z))
    (commonSupportEnergyMemLp a ha) (commonSupportEnergyMemLp a1 ha1)
    1 r 0 U hU h0U hInv hInv0 (hASmooth.differentiable (by simp) 0) hTDiff hT1Diff
    CW 5 (weakFullDerivativeBudget*DA*L) (9*(P+Q)) (9*P)
    (weakFullDerivativeBudget*D1*L) (weakFullDerivativeBudget*DQ*L) CP2
    hr hr1 hCW (by norm_num) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hCP2 hNI hNI0 hNA hNB hNV1 hND1 hNDQ hBulkPoint
  refine ⟨U,hU,h0U,hInv,hPDiff,hP1Diff,hDP1.trans_eq ?_,hBound.trans_eq ?_⟩
  · ring
  · dsimp only [commonSupportWeakTaylorDerivativeBudget]
    ring

end ShrinkingSpheres
