import Proof.CommonSupportWeakAffineHigherJets
import Proof.PoissonAffineRemainderHigherJets
import Proof.WeakPoissonTaylorDerivative
import Proof.CommonSupportPoissonHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem commonSupport_weak_poisson_taylor_eq_correction
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (r : ℝ) :
    (fun t => commonSupportWeakHalfLift a ha t-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) =
    fun t => -((TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL.comp
      ((commonSupportZeroWeakEnergy a ha t).inverse.comp
        ((commonSupportWeakEnergy a ha t).comp fixedHarmonicH1LiftL)-
        r • (nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).inverse.comp
          ((commonSupportWeakEnergy a1 ha1 t).comp fixedHarmonicH1LiftL))) := by
  funext t
  have he := nativeWeakHalfLift_first_remainder_eq_zero (fun z => a (t,z)) (fun z => a1 (t,z))
    (commonSupportEnergyMemLp a ha t) (commonSupportEnergyMemLp a1 ha1 t) 1 r
  delta commonSupportWeakHalfLift commonSupportZeroWeakEnergy commonSupportWeakEnergy
  dsimp only [nativeWeakPoissonZeroFirstRemainderL] at he
  convert he using 1

def weakPoissonTaylorJetBudget (N : ℕ) (CI C0 qA P1 QR : ℝ) : ℝ :=
  let WB := weakFullDerivativeBudget
  let RB := 9+WB
  ‖((TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL : BallH1Zero →L[ℝ] BallH1)‖*
    poissonAffineRemainderJetBudget N (inverseFamilyJetBudget N CI (WB*qA))
      C0 (WB*P1+RB*QR) (WB*P1) (RB*QR) fixedHarmonicH1LiftL

attribute [local irreducible] commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

/-- All mixed jets of the actual weak Poisson Taylor error retain r², with
    the canonical inverse and the same actual coefficient/first-model family. -/
theorem commonSupport_weak_poisson_taylor_higher_jets
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
    ‖iteratedFDeriv ℝ n (fun t => commonSupportWeakHalfLift a ha t-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) p‖ ≤
        weakPoissonTaylorJetBudget N CI C0 qA P1 QR*r^2 := by
  let WB := weakFullDerivativeBudget
  let RB := 9+WB
  let A := commonSupportZeroWeakEnergy a ha
  let A0 := nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)
  let A1 := commonSupportZeroWeakEnergy a1 ha1
  let T := commonSupportWeakEnergy a ha
  let T0 := nativeCoefficientWeakEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)
  let T1 := commonSupportWeakEnergy a1 ha1
  let CIJ := inverseFamilyJetBudget N CI (WB*qA)
  let C := poissonAffineRemainderJetBudget N CIJ C0 (WB*P1+RB*QR) (WB*P1) (RB*QR) fixedHarmonicH1LiftL
  let J : BallH1Zero →L[ℝ] BallH1 := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  let Corr := fun t => (A t).inverse.comp ((T t).comp fixedHarmonicH1LiftL)-
    r • A0.inverse.comp ((T1 t).comp fixedHarmonicH1LiftL)
  have hWB : 0 ≤ WB := weakFullDerivativeBudget_nonneg
  have hRB : 0 ≤ RB := by dsimp only [RB];positivity
  have hCIJ : 0 ≤ CIJ := inverseFamilyJetBudget_nonneg N CI (WB*qA) hCI (by positivity)
  have hA : ContDiffAt ℝ ∞ A p := (contDiff_commonSupportZeroWeakEnergy a ha S hS hz).contDiffAt
  have hA1 : ContDiffAt ℝ ∞ A1 p := (contDiff_commonSupportZeroWeakEnergy a1 ha1 S1 hS1 hz1).contDiffAt
  have hT : ContDiffAt ℝ ∞ T p := (contDiff_commonSupportWeakEnergy a ha S hS hz).contDiffAt
  have hT1 : ContDiffAt ℝ ∞ T1 p := (contDiff_commonSupportWeakEnergy a1 ha1 S1 hS1 hz1).contDiffAt
  have hInvA : (A p).IsInvertible := hInv
  have hInvCont : ContDiffAt ℝ ∞ (fun L : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => L.inverse) (A p) :=
    hInvA.contDiffAt_map_inverse
  have hAI : ContDiffAt ℝ ∞ (fun t => (A t).inverse) p := hInvCont.comp p hA
  have hCorr : ContDiffAt ℝ ∞ Corr p := (hAI.clm_comp (hT.clm_comp contDiffAt_const)).sub
    ((contDiffAt_const.clm_comp (hT1.clm_comp contDiffAt_const)).const_smul r)
  have hInvJets (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l (fun t => (A t).inverse) p‖ ≤ CIJ :=
    norm_iteratedFDeriv_inverse_family_le_of_isInvertible (P:=P) (E:=BallH1Zero) (F:=StrongDual ℝ BallH1Zero)
      A p hInv hA N CI (WB*qA) hCI (by positivity) hNI
      (fun j _ hj => norm_iteratedFDeriv_commonSupportZeroWeakEnergy_le a ha S hS hz p j qA hqA (hAJets j hj)) l hl
  have hFirstA (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l A1 p‖ ≤ WB*P1 :=
    norm_iteratedFDeriv_commonSupportZeroWeakEnergy_le a1 ha1 S1 hS1 hz1 p l P1 hP1 (hFirstJets l hl)
  have hFirstT (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l T1 p‖ ≤ WB*P1 :=
    norm_iteratedFDeriv_commonSupportWeakEnergy_le a1 ha1 S1 hS1 hz1 p l P1 hP1 (hFirstJets l hl)
  have hRem (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => A t-A0-r • A1 t) p‖ ≤ (RB*QR)*r^2 ∧
      ‖iteratedFDeriv ℝ l (fun t => T t-T0-r • T1 t) p‖ ≤ (RB*QR)*r^2 := by
    have hh := norm_iteratedFDeriv_commonSupport_weak_affine_remainder_le a a1 aD ha ha1 haD
      S S1 SD hS hS1 hSD hz hz1 hzD r hField p l (QR*r^2) (by positivity) (hRemainderJets l hl)
    exact ⟨hh.2.2.trans_eq (by dsimp only [RB,WB];ring),hh.2.1.trans_eq (by dsimp only [RB,WB];ring)⟩
  have hDiff (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l (fun t => A t-A0) p‖ ≤ (WB*P1+RB*QR)*r :=
    norm_iteratedFDeriv_difference_of_affine_remainder_le A A1 A0 p hA hA1 l r (WB*P1) (RB*QR)
      hr hr1 (by positivity) (by positivity) (hFirstA l hl) (hRem l hl).1
  have hFlatOp : T0.comp fixedHarmonicH1LiftL = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousLinearMap.ext
    intro v
    change T0 (fixedHarmonicH1LiftL f) v = 0
    dsimp only [T0]
    rw [nativeCoefficientWeakEnergyL_apply]
    exact fixedHarmonicH1Lift_flat_weak 1 f v
  have hCN (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n Corr p‖ ≤ C*r^2 :=
    norm_iteratedFDeriv_poisson_affine_remainder_le (P:=P) (E:=BallH1Zero) (F:=StrongDual ℝ BallH1Zero)
      A A0 T T1 T0 fixedHarmonicH1LiftL p hA hT hT1 hInv hInv0 hFlatOp N r CIJ C0
      (WB*P1+RB*QR) (WB*P1) (RB*QR) hr hCIJ hC0 (by positivity) (by positivity) (by positivity)
      hNI0 hInvJets hDiff hFirstT (fun l hl => (hRem l hl).2) n hn
  intro n hn
  rw [commonSupport_weak_poisson_taylor_eq_correction]
  change ‖iteratedFDeriv ℝ n (fun t => -(J.comp (Corr t))) p‖ ≤ _
  rw [norm_iteratedFDeriv_neg_at _ p (contDiffAt_const.clm_comp hCorr) n]
  exact (norm_iteratedFDeriv_operator_postcomp_fixed_le J Corr p hCorr n).trans
    ((mul_le_mul_of_nonneg_left (hCN n hn) (norm_nonneg J)).trans_eq
      (by dsimp only [weakPoissonTaylorJetBudget,C,CIJ,WB,RB,J];ring))

end ShrinkingSpheres
