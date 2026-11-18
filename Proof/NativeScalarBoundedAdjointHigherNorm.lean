import Proof.NativeScalarBoundedAdjointNorm
import Proof.TaylorScalarHighNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A higher adjoint norm budget for the SAME scalar packet and bounded remainder. -/
def nativeScalarBoundedAdjointHigherBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CK CQB CZB : ℝ) : ℝ :=
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  |(((CB+2)*‖closedThreeJetHigherScalarMultiplierL‖+
    ‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB)*CQB+CZB)|

lemma NativeScalarBoundedEndpointData.norm_adjointHigherL_le
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB scale : ℝ}
    {L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1) (hScale : 0 ≤ scale)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2) :
    ‖B.adjointHigherL ha0 KN‖ ≤ nativeScalarBoundedAdjointHigherBudget F0 ha0 CG CK CQB CZB*scale := by
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let GH := (CB+2)*‖closedThreeJetHigherScalarMultiplierL‖
  let RH := ‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB
  have hGH : 0 ≤ GH := by
    have hCB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
    dsimp only [GH,CB]
    positivity
  have hSigned : (∑ a,taylorGeneratorWeight (d.radius y) a*
      ‖signedTaylorScalarCoefficients B.coefficient a‖) ≤ CQB*scale := by
    rw [signedTaylorScalarCoefficients_weighted_sum]
    exact B.coefficient_bound
  have hHigh := (T.scalar_high_combination_norm ha0 (signedTaylorScalarCoefficients B.coefficient)).trans
    (mul_le_mul_of_nonneg_left hSigned hGH)
  have hRem := (B.norm_adjoint_remainders hF0 ha0 hCQ hCI hCW hr hr1 KN CK hCK hKN).1
  have hComp : ‖(B.adjointRemainderHalfL ha0 KN).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))‖ ≤ (RH*CQB+CZB)*scale :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _)
        (norm_nonneg (B.adjointRemainderHalfL ha0 KN))).trans_eq (mul_one _)).trans hRem)
  have hRaw : ‖B.adjointHigherL ha0 KN‖ ≤ ((GH+RH)*CQB+CZB)*scale :=
    (norm_add_le _ _).trans ((add_le_add hHigh hComp).trans_eq (by ring))
  simpa only [nativeScalarBoundedAdjointHigherBudget,GH,RH,CB,add_assoc] using
    hRaw.trans (mul_le_mul_of_nonneg_right (le_abs_self ((GH+RH)*CQB+CZB)) hScale)
end ShrinkingSpheres
