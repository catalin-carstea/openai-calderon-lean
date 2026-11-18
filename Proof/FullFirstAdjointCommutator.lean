import Proof.FullFirstAdjointRemainderNorm
import Proof.NativeScalarBoundedAdjointCommutator
import Proof.GradedLinearRemainderCommutator
import Proof.TaylorScalarLowNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Mixed adjoint commutator of the COMPLETE actual first-base coefficients.
The scalar, first-frame and physical trace corrections all use the SAME
native packet and coefficient family. The result holds for any compatible
higher endpoint of the true adjoint. -/
theorem FirstDerivativeScalarData.adjoint_commutator
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CDF CDT CQB CZB scale : ℝ}
    {D : PhysicalPrincipalData Y d CDF CDT} (B : FirstDerivativeScalarData T D CQB CZB scale)
    (hCQB : 0 ≤ CQB) (hScale : 0 ≤ scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (j k : I) (Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (D.firstDerivativeHalfL y j).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let CP := fullFirstAdjointCommonBudget F0 ha0 CG CK CQ CI CW CQB CZB
    GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (D.firstDerivativeHalfL y j).adjoint (D.firstDerivativeHalfL y k) Ha (D.firstDerivativeHigherL y k)
      ((3*C0^3*CQB^2+6*CP^2)*scale^2) := by
  have hPair := (B.endpointData j).adjoint_commutator (B.endpointData k) hCQB hScale hScale
    hF0 he ha0 hFlat hCQ hCI hCW hr hr1 KN CK hCK hKN hP Ha hHa
  simpa only [fullFirstAdjointCommonBudget,mul_assoc,← pow_two] using hPair
end ShrinkingSpheres
