import Proof.NativeScalarBoundedAdjointCommutator
import Proof.FlatRaisingScalarPacket
import Proof.FirstDerivativeScalarData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- BOTH leading/full mixed adjoint commutators, retaining genuine higher
adjoint endpoints and the actual complete physical first-base coefficient. -/
def FullFirstRaisingAdjointCrossData {Y : Set X} {d : Data} {CDF CDT : ℝ}
    (D : PhysicalPrincipalData Y d CDF CDT) (y : X) (B : ℝ) : Prop :=
  (∀ i : I,∃ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
  (∀ j : I,∃ Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hb=
      (D.firstDerivativeHalfL y j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
  ∀ i j : I,
    (∀ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
        (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
      GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
        (flatHalfRaisingL i).adjoint (D.firstDerivativeHalfL y j) Ha (D.firstDerivativeHigherL y j) B) ∧
    (∀ Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hb=
        (D.firstDerivativeHalfL y j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
      GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
        (D.firstDerivativeHalfL y j).adjoint (flatHalfRaisingL i) Hb (flatThreeHalfRaisingL i) B)

lemma FirstDerivativeScalarData.raising_adjoint_cross_data
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CDF CDT CQB CZB scale : ℝ}
    {D : PhysicalPrincipalData Y d CDF CDT} (B : FirstDerivativeScalarData T D CQB CZB scale)
    (hCQB : 0 ≤ CQB) (hCZB : 0 ≤ CZB) (hScale : 0 ≤ scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    let CQT := max (4*firstErrorScalarFixedBudget Q0) CQB
    let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let CP := nativeScalarBoundedAdjointBudget F0 ha0 CG CK CQ CI CW CQT CZB
    FullFirstRaisingAdjointCrossData D y ((3*C0^3*CQT^2+6*CP^2)*scale) := by
  let CQT := max (4*firstErrorScalarFixedBudget Q0) CQB
  let FA (i : I) : NativeScalarBoundedEndpointData T (flatHalfRaisingL i) (flatThreeHalfRaisingL i) CQT CZB 1 :=
    (T.flat_raising_scalar_packet hF0 Q0 hQ0 i).enlarge zero_le_one (le_max_left _ _) hCZB
  let FB (j : I) : NativeScalarBoundedEndpointData T (D.firstDerivativeHalfL y j) (D.firstDerivativeHigherL y j) CQT CZB scale :=
    (B.endpointData j).enlarge hScale (le_max_right _ _) le_rfl
  have hCQT : 0 ≤ CQT := hCQB.trans (le_max_right _ _)
  constructor
  · intro i
    exact ⟨(FA i).adjointHigherL ha0 KN,(FA i).adjoint_balanced_pair hF0 ha0 hFlat KN hP⟩
  constructor
  · intro j
    exact ⟨(FB j).adjointHigherL ha0 KN,(FB j).adjoint_balanced_pair hF0 ha0 hFlat KN hP⟩
  intro i j
  constructor
  · intro Ha hHa
    simpa only [mul_one] using (FA i).adjoint_commutator (FB j) hCQT zero_le_one hScale
      hF0 he ha0 hFlat hCQ hCI hCW hr hr1 KN CK hCK hKN hP Ha hHa
  · intro Hb hHb
    simpa only [mul_one] using (FB j).adjoint_commutator (FA i) hCQT hScale zero_le_one
      hF0 he ha0 hFlat hCQ hCI hCW hr hr1 KN CK hCK hKN hP Hb hHb
end ShrinkingSpheres
