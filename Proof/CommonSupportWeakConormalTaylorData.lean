import Proof.CommonSupportWeakTaylorData
import Proof.CommonSupportWeakConormalTaylorDerivative

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
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL

def commonSupportConormalTaylorDerivativeBudget (CW CA P Q CP1 CP2 DA D1 DQ : ℝ) : ℝ :=
  sphereSurfaceMass⁻¹*‖fixedHarmonicH1LiftL‖*
    (weakFullDerivativeBudget*DA*CP2+
      CA*commonSupportWeakTaylorDerivativeBudget CW P Q CP2 DA D1 DQ+
      weakFullDerivativeBudget*DA*CP1+
      (9*P+9*Q)*(5*weakFullDerivativeBudget*D1*‖fixedHarmonicH1LiftL‖)+
      weakFullDerivativeBudget*DQ*‖fixedHarmonicH1LiftL‖)

/-- Actual conormal derivative data from the same principal/first-model native
    bounds and the point weak Taylor data; no new analytic premise is added. -/
theorem commonSupport_conormal_taylor_derivative_data
    (a a1 : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r CW CA P Q CP1 CP2 DA D1 DQ L : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hCW : 0 ≤ CW) (hCA : 0 ≤ CA) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hCP1 : 0 ≤ CP1) (hCP2 : 0 ≤ CP2) (hDA : 0 ≤ DA) (hD1 : 0 ≤ D1) (hDQ : 0 ≤ DQ) (hL : 0 ≤ L)
    (F0 : SmoothCoefficientMatrix 2)
    (hNative : CommonSupportNativeDerivativeBounds a ha S hS hz (DA*r*L))
    (hNative1 : CommonSupportNativeDerivativeBounds a1 ha1 S1 hS1 hz1 (D1*L))
    (hTaylor : CommonSupportTaylorDerivativeBounds a a1 ha ha1 S S1 hS hS1 hz hz1 r F0 (DQ*r^2*L))
    (hPoint : NativeWeakTaylorData (fun z => a (0,z)) (fun z => a1 (0,z)) 1 r CW CA P Q CP1 CP2)
    (hEntries : RawAffineCoefficientBounds (fun z => a (0,z)) (fun z => a1 (0,z)) 1 r P Q) :
    ‖fderiv ℝ (fun t => commonSupportWeakConormalEndpoint a ha t-(1:ℝ) • fixedLowRadialL-
      r • weakFirstConormalVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) 0‖ ≤
      commonSupportConormalTaylorDerivativeBudget CW CA P Q CP1 CP2 DA D1 DQ*r^2*L := by
  have hWB := weakFullDerivativeBudget_nonneg
  have hN := norm_nonneg fixedHarmonicH1LiftL
  have hDS : 0 ≤ commonSupportWeakTaylorDerivativeBudget CW P Q CP2 DA D1 DQ := by
    dsimp only [commonSupportWeakTaylorDerivativeBudget]
    positivity
  obtain ⟨U,hU,h0U,hInv,hPDiff,hP1Diff,hDP1,hDPQ⟩ :=
    commonSupport_weak_taylor_derivative_data a a1 ha ha1 S S1 hS hS1 hz hz1
      r CW CA P Q CP1 CP2 DA D1 DQ L hr hr1 hCW hP hQ hCP2 hDA hD1 hDQ hL
      F0 hNative hNative1 hTaylor hPoint hEntries
  have hEDiff := (contDiff_commonSupportFullWeakEnergy a ha S hS hz).differentiable (by simp) 0
  have hE1Diff := (contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0
  have hDE : ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ (weakFullDerivativeBudget*DA*L)*r :=
    hNative.fullWeak.trans_eq (by ring)
  have hDEQ : ‖fderiv ℝ (fun t => commonSupportFullWeakEnergy a ha t-
      TauCeti.PDE.energyFormH1L (flatCoefficientBound 1)-r • commonSupportFullWeakEnergy a1 ha1 t) 0‖ ≤
      (weakFullDerivativeBudget*DQ*L)*r^2 := hTaylor.fullWeak.trans_eq (by ring)
  have hWeak : ‖fderiv ℝ (fun t => commonSupportWeakHalfLift a ha t-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) 0‖ ≤
      (commonSupportWeakTaylorDerivativeBudget CW P Q CP2 DA D1 DQ*L)*r^2 := hDPQ.trans_eq (by ring)
  have hFinal := norm_commonSupportWeakConormal_first_remainder_derivative_le a a1 ha ha1 1 r 0
    CA (weakFullDerivativeBudget*DA*L) (9*P+9*Q) CP1
    ((5*weakFullDerivativeBudget*D1*‖fixedHarmonicH1LiftL‖)*L) CP2
    (commonSupportWeakTaylorDerivativeBudget CW P Q CP2 DA D1 DQ*L)
    (weakFullDerivativeBudget*DQ*L) hEDiff hE1Diff hPDiff hP1Diff hr hr1
    hCA (by positivity) (by positivity) hCP1 (by positivity) hCP2 (by positivity) (by positivity)
    hPoint.energy.energy_bound hDE hPoint.energy_difference_bound hPoint.first_poisson_bound hDP1
    hPoint.poisson_remainder_bound hWeak hDEQ
  exact hFinal.trans_eq (by dsimp only [commonSupportConormalTaylorDerivativeBudget];ring)

end ShrinkingSpheres
