import Proof.NativeScalarBoundedEndpointData
import Proof.NativeFirstErrorAdjointEndpoints
import Proof.NativeTaylorScalarAdjointNormalForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeScalarBoundedEndpointData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
  {T : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB scale : ℝ}
  {L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
  {H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}

def adjointRemainderNegativeL (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  taylorScalarAdjointRemainderL KN
    (fun a => nativeNegativeScalarGeneratorCommutator s ha0 ((y,frameVectorLinear d.frame y),0) a (B.coefficient a))
    (B.coefficient)+(B.boundedHalf).adjoint

def adjointRemainderHalfL (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  taylorScalarAdjointRemainderHalfL KN
    (fun a => taylorGeneratorScalarCommutator T.scalar F0 ha0 a (B.coefficient a))
    (B.coefficient)+(B.boundedNegative).adjoint

def adjointHigherL (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  rightScalarCombinationL
    (taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)))
    closedThreeJetHigherScalarMultiplierL (signedTaylorScalarCoefficients (B.coefficient))+
    (B.adjointRemainderHalfL ha0 KN).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

lemma adjoint_normal_form (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    (L).adjoint=
      rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)))
        closedThreeJetHalfBoundaryScalarMultiplierL (signedTaylorScalarCoefficients (B.coefficient))+
      (B.adjointRemainderNegativeL ha0 KN).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  have hG := T.native_scalar_adjoint_normal_form hF0 ha0 hFlat KN hP (B.coefficient)
  exact low_scalar_plus_bounded_adjoint _ _ _ _ _ _ _ (B.low_form) hG
    (low_bounded_correction_adjoint _ _ _ sphereSobolevHalfNegativeInclusion_adjoint (B.bounded_pair))

lemma adjoint_remainder_compatible (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (B.adjointRemainderHalfL ha0 KN)=(B.adjointRemainderNegativeL ha0 KN).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  have hS := T.scalar_adjoint_remainder_half_negative_compatible hF0 ha0 hFlat KN hP (B.coefficient)
  have hZ := bounded_endpoint_adjoints_compatible _ (B.boundedHalf) (B.boundedNegative)
    sphereSobolevHalfNegativeInclusion_adjoint (B.bounded_pair)
  exact (ContinuousLinearMap.comp_add _ _ _).trans
    ((congrArg₂ (fun U V : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => U+V) hS hZ).trans
      (ContinuousLinearMap.add_comp _ _ _).symm)

/-- A genuine higher endpoint of the true adjoint of the full actual
first-base coefficient. Only pointwise endpoint compatibility is claimed. -/
lemma adjoint_balanced_pair (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (B.adjointHigherL ha0 KN)=
      (L).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hG := T.scalar_combination_balanced_pair hF0 (signedTaylorScalarCoefficients (B.coefficient))
  have hR := B.adjoint_remainder_compatible hF0 ha0 hFlat KN hP
  have hE := B.adjoint_normal_form hF0 ha0 hFlat KN hP
  have hR' := (ContinuousLinearMap.comp_assoc
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (B.adjointRemainderHalfL ha0 KN)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))).symm.trans
      (congrArg (fun Z => Z.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) hR)
  change _ = _
  rw [hE,ContinuousLinearMap.add_comp]
  exact (ContinuousLinearMap.comp_add _ _ _).trans
    ((congrArg₂ (fun U V : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => U+V)
      hG hR').trans (by rfl))
end NativeScalarBoundedEndpointData
end ShrinkingSpheres
