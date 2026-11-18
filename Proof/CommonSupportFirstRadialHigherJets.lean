import Proof.FirstConormalCoefficientDerivative
import Proof.LowFirstRadialDerivative
import Proof.CommonSupportBoundaryMatrixHigherJets
import Proof.CommonSupportPoissonHigherJets
import Proof.FiniteJetBudgetAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem commonSupport_weakFirstConormal_eq_fixedPost
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1) (c : ℝ) :
    (fun t => weakFirstConormalVariationL c (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) =
      fun t => fixedWeakConormalPostL.comp ((commonSupportFullWeakEnergy a1 ha1 t).comp fixedHarmonicH1LiftL) := by
  funext t
  rw [weakFirstConormal_eq_coefficient_energy]
  ext f
  rfl

attribute [local irreducible] commonSupportFullWeakEnergy

def firstConormalCoefficientJetConstant : ℝ :=
  ‖fixedWeakConormalPostL‖*‖fixedHarmonicH1LiftL‖*weakFullDerivativeBudget

def firstLowRadialJetConstant : ℝ :=
  firstConormalCoefficientJetConstant+‖fixedLowRadialL‖*(1404*boundaryHalfMultiplierBudget)

lemma firstConormalCoefficientJetConstant_nonneg : 0 ≤ firstConormalCoefficientJetConstant := by
  unfold firstConormalCoefficientJetConstant
  exact mul_nonneg (by positivity) weakFullDerivativeBudget_nonneg

lemma firstLowRadialJetConstant_nonneg : 0 ≤ firstLowRadialJetConstant := by
  unfold firstLowRadialJetConstant
  exact add_nonneg firstConormalCoefficientJetConstant_nonneg
    (mul_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) boundaryHalfMultiplierBudget_nonneg))

theorem contDiff_commonSupport_weakFirstConormal
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1)
    (S1 : Set X) (hS1 : IsCompact S1) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0) (c : ℝ) :
    ContDiff ℝ ∞ (fun t => weakFirstConormalVariationL c (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) := by
  rw [commonSupport_weakFirstConormal_eq_fixedPost a1 ha1 c]
  exact contDiff_const.clm_comp
    ((contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).clm_comp contDiff_const)

theorem norm_iteratedFDeriv_commonSupport_weakFirstConormal_le
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1)
    (S1 : Set X) (hS1 : IsCompact S1) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (c : ℝ) (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => a1 (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (fun t => weakFirstConormalVariationL c (fun z => a1 (t,z))
      (commonSupportEnergyMemLp a1 ha1 t)) p‖ ≤ firstConormalCoefficientJetConstant*q := by
  let E1 := commonSupportFullWeakEnergy a1 ha1
  let U := fun t => (E1 t).comp fixedHarmonicH1LiftL
  have hE1 : ContDiffAt ℝ ∞ E1 p := (contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).contDiffAt
  have hU : ContDiffAt ℝ ∞ U p := hE1.clm_comp contDiffAt_const
  have hEN := norm_iteratedFDeriv_commonSupportFullWeakEnergy_le a1 ha1 S1 hS1 hz1 p n q hq hJets
  have hUN := norm_iteratedFDeriv_operator_precomp_fixed_le E1 fixedHarmonicH1LiftL p hE1 n
  rw [commonSupport_weakFirstConormal_eq_fixedPost a1 ha1 c]
  exact (norm_iteratedFDeriv_operator_postcomp_fixed_le fixedWeakConormalPostL U p hU n).trans
    ((mul_le_mul_of_nonneg_left (hUN.trans (mul_le_mul_of_nonneg_left hEN (norm_nonneg _))) (norm_nonneg _)).trans_eq
      (by unfold firstConormalCoefficientJetConstant;ring))

lemma commonSupportLowFirstRadial_one_eq
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1)
    (S1 : Set X) (hS1 : IsCompact S1) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0) :
    commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1 =
      fun t => weakFirstConormalVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)-
        (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 t)).comp fixedLowRadialL := by
  funext t
  delta commonSupportLowFirstRadialL
  rw [inv_one,one_smul]

theorem contDiff_commonSupport_lowFirstRadial_one
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1)
    (S1 : Set X) (hS1 : IsCompact S1) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0) :
    ContDiff ℝ ∞ (commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1) := by
  have hN := contDiff_commonSupport_weakFirstConormal a1 ha1 S1 hS1 hz1 1
  have hM := contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a1 ha1 S1 hS1 hz1
  have hResult := hN.sub (hM.clm_comp (contDiff_const : ContDiff ℝ ∞ (fun _ : P => fixedLowRadialL)))
  rw [commonSupportLowFirstRadial_one_eq a1 ha1 S1 hS1 hz1]
  convert hResult using 1

/-- The same actual first low radial family needs no inverse jets: the first
    conormal is the coefficient energy and the first normal is linear. -/
theorem norm_iteratedFDeriv_commonSupport_lowFirstRadial_one_le
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1)
    (S1 : Set X) (hS1 : IsCompact S1) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k.val (fun z => a1 (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1) p‖ ≤ firstLowRadialJetConstant*q := by
  let N1 := fun t => weakFirstConormalVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)
  let M1 := fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 t)
  have hN : ContDiffAt ℝ ∞ N1 p := (contDiff_commonSupport_weakFirstConormal a1 ha1 S1 hS1 hz1 1).contDiffAt
  have hM : ContDiffAt ℝ ∞ M1 p :=
    (contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a1 ha1 S1 hS1 hz1).contDiffAt
  have hNE := norm_iteratedFDeriv_commonSupport_weakFirstConormal_le a1 ha1 S1 hS1 hz1 1 p n q hq
    (fun i j x hx => hJets i j ⟨0,by omega⟩ x hx)
  have hEqM : M1 = fun t => boundaryMatrixMultiplier none (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t) := by
    funext t
    exact commonSupport_negative_normal_multiplier_eq a1 ha1 S1 hS1 hz1 t
  have hMN : ‖iteratedFDeriv ℝ n M1 p‖ ≤ (1404*boundaryHalfMultiplierBudget)*q := by
    rw [hEqM]
    exact norm_iteratedFDeriv_commonSupport_boundaryMatrixMultiplier_le none a1 ha1 S1 hS1 hz1 p n q hq hJets
  rw [commonSupportLowFirstRadial_one_eq a1 ha1 S1 hS1 hz1]
  change ‖iteratedFDeriv ℝ n (fun t => N1 t-(M1 t).comp fixedLowRadialL) p‖ ≤ _
  have hMD := norm_iteratedFDeriv_operator_precomp_fixed_le M1 fixedLowRadialL p hM n
  exact (norm_iteratedFDeriv_sub_at_le N1 (fun t => (M1 t).comp fixedLowRadialL) p
    hN (hM.clm_comp contDiffAt_const) n).trans
      ((add_le_add hNE (hMD.trans (mul_le_mul_of_nonneg_left hMN (norm_nonneg _)))).trans_eq
        (by unfold firstLowRadialJetConstant;ring))

end ShrinkingSpheres
