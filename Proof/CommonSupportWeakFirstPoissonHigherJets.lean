import Proof.FiniteJetBudgetAlgebra
import Proof.WeakFirstVariationDerivative
import Proof.CommonSupportWeakEnergyHigherJets
import Proof.OperatorFamilyJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakFunctionalInverse nativeCoefficientWeakEnergyL
  commonSupportWeakEnergy

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiff_commonSupport_weakFirstPoisson
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1)
    (S1 : Set X) (hS1 : IsCompact S1) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => weakFirstPoissonVariationL c (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) := by
  rw [commonSupport_weakFirstPoisson_family_eq a1 ha1 c]
  exact (contDiff_const.clm_comp
    (contDiff_const.clm_comp ((contDiff_commonSupportWeakEnergy a1 ha1 S1 hS1 hz1).clm_comp contDiff_const))).neg

/-- Every parameter jet of the actual first weak Poisson variation uses only
    the local first coefficient family, the flat inverse norm and fixed lift. -/
theorem norm_iteratedFDeriv_commonSupport_weakFirstPoisson_le
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1)
    (S1 : Set X) (hS1 : IsCompact S1) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (c : ℝ) (p : P) (n : ℕ) (C0 q : ℝ) (hC0 : 0 ≤ C0) (hq : 0 ≤ q)
    (hInv0 : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0)
    (hJets : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => a1 (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => weakFirstPoissonVariationL c (fun z => a1 (t,z))
      (commonSupportEnergyMemLp a1 ha1 t)) p‖ ≤ C0*(weakFullDerivativeBudget*q)*‖fixedHarmonicH1LiftL‖ := by
  let J : BallH1Zero →L[ℝ] BallH1 := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  let I0 := nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  let T1 := commonSupportWeakEnergy a1 ha1
  have hT1 : ContDiffAt ℝ ∞ T1 p := (contDiff_commonSupportWeakEnergy a1 ha1 S1 hS1 hz1).contDiffAt
  have hInner : ContDiffAt ℝ ∞ (fun t => I0.comp ((T1 t).comp fixedHarmonicH1LiftL)) p :=
    contDiffAt_const.clm_comp (hT1.clm_comp contDiffAt_const)
  have hCompose (t : P) : J.comp (I0.comp ((T1 t).comp fixedHarmonicH1LiftL)) =
      (J.comp I0).comp ((T1 t).comp fixedHarmonicH1LiftL) := by ext f;rfl
  have hJI : ‖J.comp I0‖ ≤ C0 :=
    (ContinuousLinearMap.opNorm_comp_le J I0).trans
      ((mul_le_mul norm_nativeWeakZeroInclusion_le_one hInv0 (norm_nonneg _) zero_le_one).trans_eq (one_mul C0))
  rw [commonSupport_weakFirstPoisson_family_eq a1 ha1 c]
  rw [norm_iteratedFDeriv_neg_at _ p (contDiffAt_const.clm_comp hInner) n]
  change ‖iteratedFDeriv ℝ n (fun t => J.comp (I0.comp ((T1 t).comp fixedHarmonicH1LiftL))) p‖ ≤ _
  simp_rw [hCompose]
  have hN := norm_iteratedFDeriv_operator_sandwich_le (J.comp I0) fixedHarmonicH1LiftL T1 p hT1 n
  have hTN := norm_iteratedFDeriv_commonSupportWeakEnergy_le a1 ha1 S1 hS1 hz1 p n q hq hJets
  exact hN.trans ((mul_le_mul (mul_le_mul_of_nonneg_right hJI (norm_nonneg _)) hTN (norm_nonneg _) (by positivity)).trans_eq (by ring))

end ShrinkingSpheres
