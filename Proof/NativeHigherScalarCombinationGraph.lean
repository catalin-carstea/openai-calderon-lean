import Proof.NativeHigherGeneratorCommutator
import Proof.NativeTaylorGeneratorCoarseEndpoints
import Proof.HigherFiniteGeneratorCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def higherScalarCombinationCommutator (G : NativeTaylorGeneratorBounds s h hK CG)
    (Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (CMh CNh : TaylorGeneratorIndex → TaylorGeneratorIndex →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  rightMultiplierCombinationCommutatorL
    (taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p))
    (fun a b => G.higherCommutatorFamily a b p)
    (fun a => closedThreeJetHigherScalarMultiplierL (Q a))
    (fun b => closedThreeJetHigherScalarMultiplierL (R b)) CMh CNh

/-- Conditional caller for the actual finite higher commutator. Its only
    new premises are the same coefficient scalar higher inclusion squares. -/
lemma higherScalarCombinationCommutator_graph (G : NativeTaylorGeneratorBounds s h hK CG)
    (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (CMh CNh : TaylorGeneratorIndex → TaylorGeneratorIndex →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (hCM : ∀ b a,(sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (CMh b a)=
      (taylorGeneratorScalarCommutator G.scalar F0 ha0 b (Q a)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hCN : ∀ a b,(sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (CNh a b)=
      (taylorGeneratorScalarCommutator G.scalar F0 ha0 a (R b)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
    let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
    (∑ a,(Gl a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a))).comp
      (∑ b,(Gh b).comp (closedThreeJetHigherScalarMultiplierL (R b)))-
    (∑ b,(Gl b).comp (closedThreeJetHalfBoundaryScalarMultiplierL (R b))).comp
      (∑ a,(Gh a).comp (closedThreeJetHigherScalarMultiplierL (Q a)))=
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (G.higherScalarCombinationCommutator Q R CMh CNh p) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
  let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
  let KG := taylorGeneratorCommutator (G.domain.degreeFamily h hK (by norm_num) p).adjoint
    (fun i j => fderiv ℝ s.response.adjointHalfTaylor p (normalFrameRelativeAngularTangent d.γ p i j))
  let M := fun a => closedThreeJetHalfBoundaryScalarMultiplierL (Q a)
  let N := fun b => closedThreeJetHalfBoundaryScalarMultiplierL (R b)
  let Mh := fun a => closedThreeJetHigherScalarMultiplierL (Q a)
  let Nh := fun b => closedThreeJetHigherScalarMultiplierL (R b)
  let CML := fun b a => taylorGeneratorScalarCommutator G.scalar F0 ha0 b (Q a)
  let CNL := fun a b => taylorGeneratorScalarCommutator G.scalar F0 ha0 a (R b)
  have hGP (a : TaylorGeneratorIndex) : I0.comp (Gh a)=(Gl a).comp I1 :=
    balanced_endpoint_pair_of_coarse _ _ _ (G.generator_coarse_endpoints hF0 a).1
      (G.generator_coarse_endpoints hF0 a).2
  have hMP (a : TaylorGeneratorIndex) : I1.comp (Mh a)=(M a).comp I1 :=
    ContinuousLinearMap.ext (fun u => closedThreeJet_higher_scalar_multiplier_half (Q a) u)
  have hNP (b : TaylorGeneratorIndex) : I1.comp (Nh b)=(N b).comp I1 :=
    ContinuousLinearMap.ext (fun u => closedThreeJet_higher_scalar_multiplier_half (R b) u)
  have hLow := graded_finite_right_multiplier_commutator I1 Gl Gh KG M N Mh Nh CML CNL
    (G.generator_commutator_graph hF0 he)
    (fun b a => G.scalar_commutator_graph ha0 hFlat hInv0 b (Q a))
    (fun a b => G.scalar_commutator_graph ha0 hFlat hInv0 a (R b)) hMP hNP
    (fun a b => closedThreeJetHigherScalarMultiplier_commute (Q a) (R b))
  have hHigh := rightMultiplierCombinationCommutatorL_compatible I1 I0 Gl Gh KG
    (fun a b => G.higherCommutatorFamily a b p) M N Mh Nh CML CNL CMh CNh hGP
    (G.higherCommutatorFamily_compatible hΩ hF0 he) hMP hNP hCM hCN
  exact hLow.trans hHigh.symm
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
