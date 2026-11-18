import Proof.CommonSupportWeakPoissonTaylorHigherJets
import Proof.CommonSupportWeakFirstPoissonHigherJets
import Proof.ConormalEnergyTaylorHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def weakConormalTaylorJetBudget (N : ℕ) (CI C0 qA P1 QR : ℝ) : ℝ :=
  let WB := weakFullDerivativeBudget
  let RB := 9+WB
  ‖conormalEnergyTaylorPostL fixedHarmonicH1LiftL‖*
    bilinearTaylorJetBudget N
      (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 (StrongDual ℝ BallH1))
      (WB*qA) (WB*P1+RB*QR) (RB*QR) (weakPoissonTaylorJetBudget N CI C0 qA P1 QR)
      (C0*(WB*P1)*‖fixedHarmonicH1LiftL‖) fixedHarmonicH1LiftL

/-- The actual native weak conormal Taylor error preserves all finite mixed
    quadratic jets with the same coefficient, flat and first-model witnesses. -/
theorem commonSupport_weak_conormal_taylor_higher_jets
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (p : P) (N : ℕ) (CI C0 qA P1 QR : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hqA : 0 ≤ qA) (hP1 : 0 ≤ P1) (hQR : 0 ≤ QR)
    (hInv : (commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (hInv0 : (nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).IsInvertible)
    (hNI : ‖(commonSupportZeroWeakEnergy a ha p).inverse‖ ≤ CI)
    (hNI0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).inverse‖ ≤ C0)
    (hAJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ qA)
    (hFirstJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ 0 (fun z => a1 (t,z) i j) x) p‖ ≤ P1)
    (hRemainderJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ 0 (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ QR*r^2) :
    ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n (fun t => commonSupportWeakConormalEndpoint a ha t-(1:ℝ) • fixedLowRadialL-
      r • weakFirstConormalVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) p‖ ≤
        weakConormalTaylorJetBudget N CI C0 qA P1 QR*r^2 := by
  let WB := weakFullDerivativeBudget
  let RB := 9+WB
  let E := commonSupportFullWeakEnergy a ha
  let E1 := commonSupportFullWeakEnergy a1 ha1
  let E0 := TauCeti.PDE.energyFormH1L (flatCoefficientBound 1)
  let W := commonSupportWeakHalfLift a ha
  let W1 := fun t => weakFirstPoissonVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)
  have hWB : 0 ≤ WB := weakFullDerivativeBudget_nonneg
  have hRB : 0 ≤ RB := by dsimp only [RB];positivity
  have hE : ContDiffAt ℝ ∞ E p := (contDiff_commonSupportFullWeakEnergy a ha S hS hz).contDiffAt
  have hE1 : ContDiffAt ℝ ∞ E1 p := (contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).contDiffAt
  have hW : ContDiffAt ℝ ∞ W p := by
    dsimp only [W]
    rw [commonSupportWeakHalfLift_eq_affineInverseCorrection]
    exact contDiffAt_affineInverseCorrectionFamily (P:=P) (E:=BallH1Zero) (F:=StrongDual ℝ BallH1Zero)
      (U:=BallH1) (Z:=SphereSobolev (1/2:ℝ)) _ _ _ _ p hInv
      (contDiff_commonSupportZeroWeakEnergy a ha S hS hz).contDiffAt
      (contDiff_commonSupportWeakEnergy a ha S hS hz).contDiffAt
  have hW1 : ContDiffAt ℝ ∞ W1 p :=
    (contDiff_commonSupport_weakFirstPoisson a1 ha1 S1 hS1 hz1 1).contDiffAt
  have hInvFlat : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat)) 0 0
      (flatCoefficientBound 1)‖ ≤ C0 := by
    have he := nativeZeroCoefficientEnergy_inverse_eq (a:=fun _ : X => (1:ℝ) • (1:Mat)) (flatCoefficientBound 1)
    exact (congrArg norm he.symm).le.trans hNI0
  have hEJets (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l E p‖ ≤ WB*qA :=
    norm_iteratedFDeriv_commonSupportFullWeakEnergy_le a ha S hS hz p l qA hqA (hAJets l hl)
  have hE1Jets (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l E1 p‖ ≤ WB*P1 :=
    norm_iteratedFDeriv_commonSupportFullWeakEnergy_le a1 ha1 S1 hS1 hz1 p l P1 hP1 (hFirstJets l hl)
  have hERem (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => E t-E0-r • E1 t) p‖ ≤ (RB*QR)*r^2 :=
    (norm_iteratedFDeriv_commonSupport_weak_affine_remainder_le a a1 aD ha ha1 haD
      S S1 SD hS hS1 hSD hz hz1 hzD r hField p l (QR*r^2) (by positivity) (hRemainderJets l hl)).1.trans_eq
        (by dsimp only [WB,RB];ring)
  have hEDiff (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => E t-E0) p‖ ≤ (WB*P1+RB*QR)*r :=
    norm_iteratedFDeriv_difference_of_affine_remainder_le E E1 E0 p hE hE1 l r (WB*P1) (RB*QR)
      hr hr1 (by positivity) (by positivity) (hE1Jets l hl) (hERem l hl)
  have hW1Jets (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l W1 p‖ ≤ C0*(WB*P1)*‖fixedHarmonicH1LiftL‖ :=
    norm_iteratedFDeriv_commonSupport_weakFirstPoisson_le a1 ha1 S1 hS1 hz1 1 p l C0 P1 hC0 hP1
      hInvFlat (hFirstJets l hl)
  have hWRem := commonSupport_weak_poisson_taylor_higher_jets a a1 aD ha ha1 haD S S1 SD
    hS hS1 hSD hz hz1 hzD r hField p N CI C0 qA P1 QR hr hr1 hCI hC0 hqA hP1 hQR
    hInv hInv0 hNI hNI0 hAJets hFirstJets hRemainderJets
  have hCIJ := inverseFamilyJetBudget_nonneg N CI (WB*qA) hCI (by positivity)
  have hCQP : 0 ≤ weakPoissonTaylorJetBudget N CI C0 qA P1 QR := by
    unfold weakPoissonTaylorJetBudget poissonAffineRemainderJetBudget
    dsimp only
    change 0 ≤ ‖((TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL :
      BallH1Zero →L[ℝ] BallH1)‖*
      (2^N*inverseFamilyJetBudget N CI (WB*qA)*((RB*QR)+2^N*(WB*P1+RB*QR)*C0*(WB*P1))*‖fixedHarmonicH1LiftL‖)
    positivity
  have hFamily : (fun t => commonSupportWeakConormalEndpoint a ha t-(1:ℝ) • fixedLowRadialL-
      r • weakFirstConormalVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) =
      (fun t => (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
        ((E t).bilinearComp (W t) fixedHarmonicH1LiftL-E0.bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL-
          r • (E0.bilinearComp (W1 t) fixedHarmonicH1LiftL+(E1 t).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL)))) := by
    funext t
    dsimp only [E,E0,E1,W,W1]
    delta commonSupportWeakConormalEndpoint commonSupportFullWeakEnergy commonSupportWeakHalfLift
    convert nativeWeakConormal_first_remainder_eq_energy (commonSupportEnergyMemLp a ha t)
      (commonSupportEnergyMemLp a1 ha1 t) 1 r using 1
  intro n hn
  rw [hFamily]
  exact norm_iteratedFDeriv_conormal_energy_taylor_le E E1 E0 W W1 fixedHarmonicH1LiftL p hE hE1 hW hW1
    N r (WB*qA) (WB*P1+RB*QR) (RB*QR) (weakPoissonTaylorJetBudget N CI C0 qA P1 QR)
      (C0*(WB*P1)*‖fixedHarmonicH1LiftL‖) hr (by positivity) (by positivity) (by positivity) hCQP (by positivity)
      hEJets hEDiff hERem hWRem hW1Jets n hn

end ShrinkingSpheres
