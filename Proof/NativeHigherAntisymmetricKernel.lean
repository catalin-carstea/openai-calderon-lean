import Proof.NativeHigherNegativeScalarCompatibility
import Proof.ConjugationKernelEndpointCompatibility
import Proof.HigherDegreeScalarLinearity
import Proof.ScalarNormalExpansionAlgebra
import Proof.NativeAntisymmetricTaylorGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def antisymmetricTaylorHigherFromRotationData
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q Qell : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R Rell : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  -(closedThreeJetHigherScalarMultiplierL (Q p)).inverse.comp
    (A.fullAdjointScalarHigherFromRotationData ha0 Q R p)+
    d.radius y • A.higherScalarGeneratorFromRotationData ha0 .degree Qell Rell p

lemma antisymmetricTaylorHigherFromRotationData_negative_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q Qell : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R Rell : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0)))
    (hRell : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (Rell (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Qell ((y,frameVectorLinear d.frame y),0)))
    (hM : (closedThreeJetHigherScalarMultiplierL (Q ((y,frameVectorLinear d.frame y),0))).IsInvertible)
    (hMN : (closedThreeJetNegativeScalarMultiplierL (Q ((y,frameVectorLinear d.frame y),0))).IsInvertible) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let IHN := sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    IHN.comp (A.antisymmetricTaylorHigherFromRotationData ha0 Q Qell R Rell p)=
      (s.response.antisymmetricTaylorKernel F0 ha0 (Q p) (Qell p) p).comp IHN := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let IHN := sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hMI : IHN.comp (closedThreeJetHigherScalarMultiplierL (Q p))=
      (closedThreeJetNegativeScalarMultiplierL (Q p)).comp IHN :=
    ContinuousLinearMap.ext (closedThreeJet_higher_scalar_multiplier_negative (Q p))
  exact conjugation_taylor_kernel_endpoint_compatible IHN _ _ _ _ _ _ (d.radius y) hM hMN hMI
    (A.fullAdjointScalarHigherFromRotationData_negative_compatible G ha0 H hF0 Q R hR)
    (A.higherScalarGeneratorFromRotationData_negative_compatible G ha0 H hF0 .degree Qell Rell hRell)

lemma antisymmetricTaylorHigherFromRotationData_half_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q Qell : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R Rell : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0)))
    (hRell : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (Rell (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Qell ((y,frameVectorLinear d.frame y),0)))
    (hM : (closedThreeJetHigherScalarMultiplierL (Q ((y,frameVectorLinear d.frame y),0))).IsInvertible)
    (hMN : (closedThreeJetNegativeScalarMultiplierL (Q ((y,frameVectorLinear d.frame y),0))).IsInvertible)
    (hSkew : let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      let KN := s.response.antisymmetricTaylorKernel F0 ha0 (Q p) (Qell p) p
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))=
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let KN := s.response.antisymmetricTaylorKernel F0 ha0 (Q p) (Qell p) p
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.antisymmetricTaylorHigherFromRotationData ha0 Q Qell R Rell p)=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  higher_negative_skew_kernel_half_compatible _ _
    (A.antisymmetricTaylorHigherFromRotationData_negative_compatible G ha0 H hF0 Q Qell R Rell hR hRell hM hMN) hSkew

lemma antisymmetricTaylorHigherFromRotationData_norm_of_expansion
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q Qell : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R Rell : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter) (CI BM BR : ℝ)
    (hM : (closedThreeJetHigherScalarMultiplierL (Q p)).IsInvertible)
    (hr : 0 ≤ d.radius y) (hCI : 0 ≤ CI)
    (hInv : ‖(closedThreeJetHigherScalarMultiplierL (Q p)).inverse‖ ≤ CI)
    (hSmall : ‖closedThreeJetHigherScalarMultiplierL (Q p)-ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ))‖ ≤ BM*d.radius y)
    (Rest : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (hExpand : A.fullAdjointScalarHigherFromRotationData ha0 Q R p=
      d.radius y • A.higherScalarGeneratorFromRotationData ha0 .degree Qell Rell p+Rest)
    (hRest : ‖Rest‖ ≤ BR*(d.radius y)^2) :
    ‖A.antisymmetricTaylorHigherFromRotationData ha0 Q Qell R Rell p‖ ≤
      CI*(BM*‖A.higherScalarGeneratorFromRotationData ha0 .degree Qell Rell p‖+BR)*(d.radius y)^2 := by
  unfold antisymmetricTaylorHigherFromRotationData
  rw [hExpand]
  exact norm_conjugation_taylor_cancellation _ _ _ hM (d.radius y) CI BM BR hr hCI hInv hSmall hRest
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
