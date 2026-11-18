import Proof.FullFirstAdjointCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Pointwise full-coefficient mixed adjoint data. Existence and the bound
refer to the actual selected physical coefficient and its genuine higher
endpoint; no global parameter smoothness is included. -/
def FullFirstAdjointCommutatorData {Y : Set X} {d : Data} {CDF CDT : ℝ}
    (D : PhysicalPrincipalData Y d CDF CDT) (y : X) (B : ℝ) : Prop :=
  (∀ j : I,∃ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (D.firstDerivativeHalfL y j).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
  ∀ j k : I,∀ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (D.firstDerivativeHalfL y j).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
    GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (D.firstDerivativeHalfL y j).adjoint (D.firstDerivativeHalfL y k) Ha (D.firstDerivativeHigherL y k) B

lemma FirstDerivativeScalarData.adjoint_commutator_data
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
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let CP := fullFirstAdjointCommonBudget F0 ha0 CG CK CQ CI CW CQB CZB
    FullFirstAdjointCommutatorData D y ((3*C0^3*CQB^2+6*CP^2)*scale^2) := by
  constructor
  · intro j
    exact ⟨B.adjointHigherL ha0 KN j,B.adjoint_balanced_pair hF0 ha0 hFlat KN hP j⟩
  · intro j k Ha hHa
    exact B.adjoint_commutator hCQB hScale hF0 he ha0 hFlat hCQ hCI hCW hr hr1 KN CK hCK hKN hP j k Ha hHa
end ShrinkingSpheres
