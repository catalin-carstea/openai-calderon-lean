import Proof.FullFirstAdjointScalarForm
import Proof.NativeScalarBoundedAdjointNorm
import Proof.NativeAdjointRemainderHalfNorm
import Proof.NativeTaylorScalarAdjointRemainderBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A common budget for generator norms, both adjoint remainders and the
unsigned bounded correction of the full actual first-base coefficient. -/
def fullFirstAdjointCommonBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CK CQ CI CW CQB CZB : ℝ) : ℝ :=
  nativeScalarBoundedAdjointBudget F0 ha0 CG CK CQ CI CW CQB CZB

lemma fullFirstAdjointCommonBudget_bounds (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CK CQ CI CW CQB CZB : ℝ) :
    let CB := taylorGeneratorFixedBudget F0 ha0 CG
    let CP := fullFirstAdjointCommonBudget F0 ha0 CG CK CQ CI CW CQB CZB
    1 ≤ CP ∧ CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CQB ≤ CP ∧
    (‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB)*CQB+CZB ≤ CP ∧
    (‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW)*CQB+CZB ≤ CP ∧
    CZB ≤ CP := by
  exact nativeScalarBoundedAdjointBudget_bounds F0 ha0 CG CK CQ CI CW CQB CZB

lemma FirstDerivativeScalarData.norm_adjoint_remainders
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CDF CDT CQB CZB scale : ℝ}
    {D : PhysicalPrincipalData Y d CDF CDT} (B : FirstDerivativeScalarData T D CQB CZB scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2) (j : I) :
    let CB := taylorGeneratorFixedBudget F0 ha0 CG
    ‖B.adjointRemainderHalfL ha0 KN j‖ ≤
      ((‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB)*CQB+CZB)*scale ∧
    ‖B.adjointRemainderNegativeL ha0 KN j‖ ≤
      ((‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW)*CQB+CZB)*scale := by
  exact (B.endpointData j).norm_adjoint_remainders hF0 ha0 hCQ hCI hCW hr hr1 KN CK hCK hKN
end ShrinkingSpheres
