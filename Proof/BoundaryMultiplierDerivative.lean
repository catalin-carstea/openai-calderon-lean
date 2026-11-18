import Proof.CommonSupportMultiplierDerivative
import Proof.BoundaryCoefficientMultiplierAlgebra
import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

/-- A fixed trace/lift constant for local C1 coefficient derivative bounds. -/
def boundaryHalfDerivativeBudget : ℝ := 4*‖fixedHalfValueTraceL‖*‖fixedHarmonicH1LiftL‖

lemma boundaryHalfDerivativeBudget_nonneg : 0 ≤ boundaryHalfDerivativeBudget := by
  unfold boundaryHalfDerivativeBudget
  positivity

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The genuine half-order boundary multiplier derivative needs only local
    value and first spatial parameter jets. -/
theorem norm_fderiv_commonSupport_halfBoundaryCoefficientMul_le
    (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → g (p,z) = 0) (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ j : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ j.val (fun z => g (t,z)) x) p‖ ≤ q) :
    ‖fderiv ℝ (fun t => halfBoundaryCoefficientMulL
      (commonSupportCoefficientFamily 2 g hg K hK hz t)) p‖ ≤ boundaryHalfDerivativeBudget*q := by
  let M := fun t => coefficientMultiplier fixedSobolevCalculus 1
    (commonSupportCoefficientFamily 2 g hg K hK hz t)
  have hM := (contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 1
    g hg K hK hz).differentiable (by simp) p
  have hMN := norm_fderiv_commonSupport_coefficientMultiplier_one_le fixedSobolevCalculus
    g hg K hK hz p q hq hJets
  have hEq : (fun t => halfBoundaryCoefficientMulL
      (commonSupportCoefficientFamily 2 g hg K hK hz t)) =
      fun t => fixedHalfValueTraceL.comp ((M t).comp fixedHarmonicH1LiftL) := by
    funext t
    rfl
  rw [hEq]
  have hPre := norm_fderiv_clm_comp_le M (fun _ : P => fixedHarmonicH1LiftL) p hM (differentiableAt_const _)
  have hPost := norm_fderiv_clm_comp_le (fun _ : P => fixedHalfValueTraceL)
    (fun t => (M t).comp fixedHarmonicH1LiftL) p (differentiableAt_const _)
      (hM.clm_comp (differentiableAt_const _))
  simp only [fderiv_const_apply,norm_zero,zero_mul,mul_zero,zero_add,add_zero] at hPre hPost
  have hInner : ‖fderiv ℝ (fun t => (M t).comp fixedHarmonicH1LiftL) p‖ ≤ (4*q)*‖fixedHarmonicH1LiftL‖ :=
    hPre.trans (mul_le_mul_of_nonneg_right hMN (norm_nonneg _))
  exact hPost.trans ((mul_le_mul_of_nonneg_left hInner (norm_nonneg _)).trans_eq
    (by unfold boundaryHalfDerivativeBudget;ring))

/-- Hilbert duality preserves the same local derivative budget at the negative
    half endpoint; all operators are the actual supplied coefficient maps. -/
theorem norm_fderiv_commonSupport_negativeBoundaryCoefficientMul_le
    (g : P × X → ℝ) (hg : ContDiff ℝ ∞ g) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → g (p,z) = 0) (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJets : ∀ j : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ j.val (fun z => g (t,z)) x) p‖ ≤ q) :
    ‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL
      (commonSupportCoefficientFamily 2 g hg K hK hz t)) p‖ ≤ boundaryHalfDerivativeBudget*q := by
  let M := fun t => halfBoundaryCoefficientMulL (commonSupportCoefficientFamily 2 g hg K hK hz t)
  have hM : DifferentiableAt ℝ M p :=
    (contDiff_nativeHalfCoefficientMulL_commonSupport fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace g hg K hK hz).differentiable (by simp) p
  have hN := norm_fderiv_commonSupport_halfBoundaryCoefficientMul_le g hg K hK hz p q hq hJets
  have hD := (realHalfOperatorAdjointL.hasFDerivAt.comp p hM.hasFDerivAt).fderiv
  change fderiv ℝ (fun t => realHalfOperatorAdjointL (M t)) p = _ at hD
  change ‖fderiv ℝ (fun t => realHalfOperatorAdjointL (M t)) p‖ ≤ _
  rw [hD]
  have hAdj : ‖realHalfOperatorAdjointL‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    change ‖ContinuousLinearMap.adjoint A‖ ≤ 1*‖A‖
    simpa only [one_mul] using (ContinuousLinearMap.adjoint.norm_map A).le
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hAdj hN (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

end ShrinkingSpheres
