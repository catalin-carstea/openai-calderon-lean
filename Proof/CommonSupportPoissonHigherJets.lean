import Proof.AffineInverseFamilyJetBounds
import Proof.CommonSupportOperatorHigherJets
import Proof.CommonSupportWeakEnergyHigherJets
import Proof.CommonSupportWeakPoissonRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def strongPoissonJetBudget (N : ℕ) (I q : ℝ) : ℝ :=
  affineInverseCorrectionJetBudget N I (2*strongC1OperatorBudget fixedSobolevCalculus*q)
    (2*fullC1OperatorBudget fixedSobolevCalculus*q) fixedStrongH2InclusionL fixedHarmonicLiftL

/-- All finite jets of the actual strong Poisson family from local coefficient
    jets and the point inverse norm, with no exterior-cutoff budget. -/
theorem norm_iteratedFDeriv_commonSupport_strongPoissonL_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (N : ℕ) (I q : ℝ) (hI : 0 ≤ I) (hq : 0 ≤ q)
    (hAx : (strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha K hK hz p)).IsInvertible)
    (hInv : ‖(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha K hK hz p)).inverse‖ ≤ I)
    (hJets : ∀ l : ℕ,l ≤ N → ∀ i j : ShrinkingSpheres.I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ q)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun t => strongPoissonL (commonSupportMatrixFamily 2 a ha K hK hz t)) p‖ ≤
      strongPoissonJetBudget N I q := by
  let A := fun t => strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha K hK hz t)
  let B := fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha K hK hz t)
  have hA : ContDiffAt ℝ ∞ A p :=
    (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha K hK hz).contDiffAt
  have hB : ContDiffAt ℝ ∞ B p := (contDiff_commonSupport_fullCoefficientOperator 0 a ha K hK hz).contDiffAt
  have hEq : (fun t => strongPoissonL (commonSupportMatrixFamily 2 a ha K hK hz t)) =
      affineInverseCorrectionFamily fixedStrongH2InclusionL fixedHarmonicLiftL A B := by
    funext t
    ext f
    rfl
  rw [hEq]
  exact norm_iteratedFDeriv_affineInverseCorrectionFamily_le fixedStrongH2InclusionL fixedHarmonicLiftL
    A B p hAx hA hB N I (2*strongC1OperatorBudget fixedSobolevCalculus*q)
      (2*fullC1OperatorBudget fixedSobolevCalculus*q) hI
      (by have hh := strongC1OperatorBudget_nonneg fixedSobolevCalculus;positivity)
      (by have hh := fullC1OperatorBudget_nonneg fixedSobolevCalculus;positivity) hInv
      (fun l _ hl => norm_iteratedFDeriv_commonSupport_strongOperator_zero_le fixedSobolevCalculus
        a ha K hK hz p l q hq (hJets l hl))
      (fun l hl => norm_iteratedFDeriv_commonSupport_fullOperator_zero_le fixedSobolevCalculus
        a ha K hK hz p l q hq (hJets l hl)) n hn

def weakPoissonJetBudget (N : ℕ) (I q : ℝ) : ℝ :=
  affineInverseCorrectionJetBudget N I (weakFullDerivativeBudget*q) (weakFullDerivativeBudget*q)
    (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
      (harmonicFirstOrderLiftCompletion sphereFischerInner)

theorem commonSupportWeakHalfLift_eq_affineInverseCorrection
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) :
    commonSupportWeakHalfLift a ha = affineInverseCorrectionFamily
      (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
      (harmonicFirstOrderLiftCompletion sphereFischerInner)
      (commonSupportZeroWeakEnergy a ha) (commonSupportWeakEnergy a ha) := by
  funext p
  change ((ContinuousLinearMap.id ℝ BallH1)-
    (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL.comp
      ((nativeZeroFunctionalInverse (commonSupportZeroWeakEnergy a ha p)).comp
        (commonSupportWeakEnergy a ha p))).comp (harmonicFirstOrderLiftCompletion sphereFischerInner) = _
  rw [nativeZeroFunctionalInverse_eq_map_inverse]
  ext f
  rfl

def fixedWeakConormalPostL : StrongDual ℝ BallH1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip
      (harmonicFirstOrderLiftCompletion sphereFischerInner))

lemma commonSupportWeakConormalEndpoint_eq_fixedPost
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) :
    commonSupportWeakConormalEndpoint a ha = fun t => fixedWeakConormalPostL.comp
      ((commonSupportFullWeakEnergy a ha t).comp (commonSupportWeakHalfLift a ha t)) := by
  funext t
  ext1 f
  rfl

attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

/-- The actual weak Poisson lift uses the same coefficient family and the
    canonical inverse of its actual zero-boundary energy map. -/
theorem norm_iteratedFDeriv_commonSupportWeakHalfLift_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (N : ℕ) (I q : ℝ) (hI : 0 ≤ I) (hq : 0 ≤ q)
    (hAx : (commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (hInv : ‖(commonSupportZeroWeakEnergy a ha p).inverse‖ ≤ I)
    (hJets : ∀ l : ℕ,l ≤ N → ∀ i j : ShrinkingSpheres.I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (commonSupportWeakHalfLift a ha) p‖ ≤ weakPoissonJetBudget N I q := by
  rw [commonSupportWeakHalfLift_eq_affineInverseCorrection]
  have hD : 0 ≤ weakFullDerivativeBudget*q := mul_nonneg weakFullDerivativeBudget_nonneg hq
  exact norm_iteratedFDeriv_affineInverseCorrectionFamily_le (P:=P) (E:=BallH1Zero)
    (F:=StrongDual ℝ BallH1Zero) (U:=BallH1) (Z:=SphereSobolev (1/2:ℝ))
    (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
    (harmonicFirstOrderLiftCompletion sphereFischerInner) (commonSupportZeroWeakEnergy a ha)
    (commonSupportWeakEnergy a ha) p hAx
    (contDiff_commonSupportZeroWeakEnergy a ha K hK hz).contDiffAt
    (contDiff_commonSupportWeakEnergy a ha K hK hz).contDiffAt
    N I (weakFullDerivativeBudget*q) (weakFullDerivativeBudget*q) hI hD hD hInv
    (fun l _ hl => norm_iteratedFDeriv_commonSupportZeroWeakEnergy_le a ha K hK hz p l q hq (hJets l hl))
    (fun l hl => norm_iteratedFDeriv_commonSupportWeakEnergy_le a ha K hK hz p l q hq (hJets l hl)) n hn

lemma weakPoissonJetBudget_nonneg (N : ℕ) (I q : ℝ) (hI : 0 ≤ I) (hq : 0 ≤ q) :
    0 ≤ weakPoissonJetBudget N I q :=
  affineInverseCorrectionJetBudget_nonneg N I (weakFullDerivativeBudget*q) (weakFullDerivativeBudget*q)
    hI (mul_nonneg weakFullDerivativeBudget_nonneg hq) (mul_nonneg weakFullDerivativeBudget_nonneg hq) _ _


def weakConormalJetBudget (N : ℕ) (I q : ℝ) : ℝ :=
  ‖fixedWeakConormalPostL‖*(2^N*(weakFullDerivativeBudget*q)*weakPoissonJetBudget N I q)

theorem norm_iteratedFDeriv_commonSupportWeakConormalEndpoint_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (N : ℕ) (I q : ℝ) (hI : 0 ≤ I) (hq : 0 ≤ q)
    (hAx : (commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (hInv : ‖(commonSupportZeroWeakEnergy a ha p).inverse‖ ≤ I)
    (hJets : ∀ l : ℕ,l ≤ N → ∀ i j : ShrinkingSpheres.I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (commonSupportWeakConormalEndpoint a ha) p‖ ≤ weakConormalJetBudget N I q := by
  let W := commonSupportWeakHalfLift a ha
  let E := commonSupportFullWeakEnergy a ha
  have hW : ContDiffAt ℝ ∞ W p := by
    dsimp only [W]
    rw [commonSupportWeakHalfLift_eq_affineInverseCorrection]
    exact contDiffAt_affineInverseCorrectionFamily (P:=P) (E:=BallH1Zero)
      (F:=StrongDual ℝ BallH1Zero) (U:=BallH1) (Z:=SphereSobolev (1/2:ℝ)) _ _ _ _ p hAx
      (contDiff_commonSupportZeroWeakEnergy a ha K hK hz).contDiffAt
      (contDiff_commonSupportWeakEnergy a ha K hK hz).contDiffAt
  have hE : ContDiffAt ℝ ∞ E p := (contDiff_commonSupportFullWeakEnergy a ha K hK hz).contDiffAt
  let C := fun t => (E t).comp (W t)
  let L := (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) (StrongDual ℝ BallH1)
    (SphereSobolev (-(1/2:ℝ)))) fixedWeakConormalPostL
  have hLN : ‖L‖ ≤ ‖fixedWeakConormalPostL‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro A
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hEq : commonSupportWeakConormalEndpoint a ha = L ∘ C := by
    rw [commonSupportWeakConormalEndpoint_eq_fixedPost]
    rfl
  have hD : 0 ≤ weakFullDerivativeBudget*q := mul_nonneg weakFullDerivativeBudget_nonneg hq
  have hCN := norm_iteratedFDeriv_operator_comp_common_bound E W p hE hW N
    (weakFullDerivativeBudget*q) (weakPoissonJetBudget N I q) hD (weakPoissonJetBudget_nonneg N I q hI hq)
    (fun l hl => norm_iteratedFDeriv_commonSupportFullWeakEnergy_le a ha K hK hz p l q hq (hJets l hl))
    (fun l hl => norm_iteratedFDeriv_commonSupportWeakHalfLift_le a ha K hK hz p N I q hI hq hAx hInv hJets l hl) n hn
  rw [hEq]
  exact (norm_iteratedFDeriv_clm_comp_le L C p (hE.clm_comp hW) n).trans
    (mul_le_mul hLN hCN (norm_nonneg _) (norm_nonneg _))

end ShrinkingSpheres
