import Proof.TaylorScalarAdjointNormalForm
import Proof.NegativeScalarGeneratorCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual native scalar-generator expression has the same signed
generators after dual-half adjunction. Its reordering remainder is the
explicit negative-endpoint operator, not an additional commutator premise.
The Taylor transpose defect is supplied by
`uniform_native_adjoint_half_taylor_defect`. -/
lemma NativeTaylorGeneratorBounds.native_scalar_adjoint_normal_form
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp
      (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))).adjoint=
      (∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp
        (closedThreeJetHalfBoundaryScalarMultiplierL (signedTaylorScalarCoefficients Q a)))+
      (taylorScalarAdjointRemainderL KN (fun a => nativeNegativeScalarGeneratorCommutator s ha0 p a (Q a)) Q).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  exact taylor_scalar_adjoint_normal_form _ KN hP Q _
    (fun a => A.generator_negative_scalar_commutator hF0 ha0 hFlat s.point.flatStrong a (Q a))
end ShrinkingSpheres
