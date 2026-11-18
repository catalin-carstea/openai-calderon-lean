import Proof.AdjointMultiplierGainGraph
import Proof.RadialMultiplierGainPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

/-- The SAME actual forward gain supplies a quadratic negative-half
commutator gain for every genuine L2 adjoint response, subtracting exactly
the adjoint of the SAME canonical bounded first radial correction. -/
theorem RadialMultiplierGainData.adjoint_gain
    {F F0 F1 : SmoothCoefficientMatrix 2}
    {ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)}
    {ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)}
    {ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)}
    {ell : X →L[ℝ] ℝ} {Q : SmoothCoefficientJets 3} {r C : ℝ}
    (t : RadialMultiplierGainData F F0 F1 ha ha0 ha1 ell Q r C)
    (R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hHigh : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F) =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hAdj : ∀ u v : SphereSobolev 1,
      ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ) :
    ∃ Ga : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖Ga‖ ≤ C*r^2 ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        ((Ra-r • ((radialCorrectionCovectorL ell).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)))).comp
          (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q))-
          (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))).comp
            (Ra-r • ((radialCorrectionCovectorL ell).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))))) =
      Ga.comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num)) := by
  let G := radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r
  let Ga := -realHalfOperatorAdjointL G
  let B := radialCorrectionCovectorL ell
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let RQ := R-r • B.comp I0
  let RaQ := Ra-r • B.adjoint.comp I0
  have hNorm : ‖Ga‖ = ‖G‖ := by
    change ‖-(ContinuousLinearMap.adjoint G)‖ = ‖G‖
    rw [norm_neg]
    exact ContinuousLinearMap.adjoint.norm_map G
  have hAdjQ (u v : SphereSobolev 1) : ⟪RQ u,I0 v⟫_ℝ = ⟪I0 u,RaQ v⟫_ℝ := by
    change ⟪R u-r • B (I0 u),I0 v⟫_ℝ = ⟪I0 u,Ra v-r • B.adjoint (I0 v)⟫_ℝ
    rw [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hAdj u v,
      ContinuousLinearMap.adjoint_inner_right]
  refine ⟨Ga,hNorm.le.trans t.norm_bound,?_⟩
  exact adjoint_multiplier_gain_graph RQ RaQ G Q hAdjQ (t.midpoint_graph R hHigh)

/-- Negative-half dual adjunction preserves the operator parameter
 derivative bound exactly, so the true adjoint gained family needs no
 additional PDE differentiation or larger constant. -/
theorem norm_fderiv_negativeHalfAdjoint_gain_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (x : P) (hG : DifferentiableAt ℝ G x) (C : ℝ) (hBound : ‖fderiv ℝ G x‖ ≤ C) :
    ‖fderiv ℝ (fun p => -realHalfOperatorAdjointL (G p)) x‖ ≤ C := by
  let J := -realHalfOperatorAdjointL
  have hJN : ‖J‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    change ‖-(ContinuousLinearMap.adjoint A)‖ ≤ 1*‖A‖
    rw [norm_neg,ContinuousLinearMap.adjoint.norm_map,one_mul]
  have hD : fderiv ℝ (fun p => -realHalfOperatorAdjointL (G p)) x = J.comp (fderiv ℝ G x) :=
    (J.hasFDerivAt.comp x hG.hasFDerivAt).fderiv
  rw [hD]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (((mul_le_mul_of_nonneg_right hJN (norm_nonneg _)).trans_eq (one_mul _)).trans hBound)

end ShrinkingSpheres
