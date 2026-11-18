import Proof.CommonSupportFullWeakEnergyDerivative
import Proof.ClosedLocalZeroMultiplier
import Proof.CommonSupportWeakEnergyRegularity
import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma fderiv_bilinear_apply_const {Q E F : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : Q → E →L[ℝ] F →L[ℝ] ℝ) (p b : Q) (u : E) (v : F)
    (hB : DifferentiableAt ℝ B p) :
    fderiv ℝ (fun t => B t u v) p b = fderiv ℝ B p b u v := by
  have hD := ((hB.hasFDerivAt.clm_apply (hasFDerivAt_const u p)).clm_apply
    (hasFDerivAt_const v p)).fderiv
  have hAt := congrArg (fun L : Q →L[ℝ] ℝ => L b) hD
  simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_apply,zero_add,map_zero,add_zero] using hAt


/-- Restricting the test argument of the genuine full form does not enlarge
    the parameter derivative estimate. The scalar evaluation proof preserves
    the native inherited normed structures. -/
theorem norm_fderiv_commonSupportWeakEnergy_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖fderiv ℝ (commonSupportWeakEnergy a ha) p‖ ≤ weakFullDerivativeBudget*q := by
  have hWD := (contDiff_commonSupportWeakEnergy a ha K hK hz).differentiable (by simp) p
  have hFD := (contDiff_commonSupportFullWeakEnergy a ha K hK hz).differentiable (by simp) p
  have hN := norm_fderiv_commonSupportFullWeakEnergy_le a ha K hK hz p q hq hJet
  have hC : 0 ≤ weakFullDerivativeBudget*q := mul_nonneg weakFullDerivativeBudget_nonneg hq
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro b
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hC (norm_nonneg b))
  intro u v
  have hEq : (fun t => commonSupportWeakEnergy a ha t u v) =
      (fun t => commonSupportFullWeakEnergy a ha t u (v:BallH1)) := by
    funext t
    exact congrArg (fun L : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero => L u v)
      (commonSupportWeakEnergy_restriction a ha t)
  have hAt := congrArg (fun f : P → ℝ => fderiv ℝ f p b) hEq
  have hLeft := fderiv_bilinear_apply_const (commonSupportWeakEnergy a ha) p b u v hWD
  have hRight := fderiv_bilinear_apply_const (commonSupportFullWeakEnergy a ha) p b u (v:BallH1) hFD
  have hPoint := hLeft.symm.trans (hAt.trans hRight)
  refine (congrArg norm hPoint).le.trans ?_
  exact (ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (commonSupportFullWeakEnergy a ha) p b) u (v:BallH1)).trans
    (by have h := (ContinuousLinearMap.le_opNorm (fderiv ℝ (commonSupportFullWeakEnergy a ha) p) b).trans
          (mul_le_mul_of_nonneg_right hN (norm_nonneg b))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg u)) (norm_nonneg v))


/-- Restricting also the solution argument preserves the same local zeroth-jet
    derivative budget for the genuine zero-boundary energy operator. -/
theorem norm_fderiv_commonSupportZeroWeakEnergy_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖fderiv ℝ (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) p‖ ≤ weakFullDerivativeBudget*q := by
  have hZD := (contDiff_commonSupportZeroWeakEnergy a ha K hK hz).differentiable (by simp) p
  have hWD := (contDiff_commonSupportWeakEnergy a ha K hK hz).differentiable (by simp) p
  have hN := norm_fderiv_commonSupportWeakEnergy_le a ha K hK hz p q hq hJet
  have hC : 0 ≤ weakFullDerivativeBudget*q := mul_nonneg weakFullDerivativeBudget_nonneg hq
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro b
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hC (norm_nonneg b))
  intro u v
  have hEq : (fun t => commonSupportZeroWeakEnergy a ha t u v) =
      (fun t => commonSupportWeakEnergy a ha t (u:BallH1) v) := by
    funext t
    exact congrArg (fun L : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => L u v)
      (commonSupportZeroWeakEnergy_restriction a ha t)
  have hAt := congrArg (fun f : P → ℝ => fderiv ℝ f p b) hEq
  have hLeft := fderiv_bilinear_apply_const (commonSupportZeroWeakEnergy a ha) p b u v hZD
  have hRight := fderiv_bilinear_apply_const (commonSupportWeakEnergy a ha) p b (u:BallH1) v hWD
  have hPoint := hLeft.symm.trans (hAt.trans hRight)
  refine (congrArg norm hPoint).le.trans ?_
  exact (ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (commonSupportWeakEnergy a ha) p b) (u:BallH1) v).trans
    (by have h := (ContinuousLinearMap.le_opNorm (fderiv ℝ (commonSupportWeakEnergy a ha) p) b).trans
          (mul_le_mul_of_nonneg_right hN (norm_nonneg b))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg u)) (norm_nonneg v))

end ShrinkingSpheres
