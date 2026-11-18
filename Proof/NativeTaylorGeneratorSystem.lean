import Proof.UniformNativeTaylorGeneratorBounds
import Proof.GradedRotationDegreeAlgebra
import Proof.FixedGeneratorScalarCommutators
import Proof.GradedFiniteGeneratorCommutator
import Proof.ClosedScalarCommutativity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

inductive TaylorGeneratorIndex where
  | taylor
  | degree
  | rotation (i j : I)
  deriving DecidableEq, Fintype

def taylorGeneratorLow (P : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    TaylorGeneratorIndex → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  | .taylor => P
  | .degree => sphereSobolevShiftedDegreeL (1/2:ℝ)
  | .rotation i j => sphereSobolevRotationL (1/2:ℝ) i j

def taylorGeneratorHigh (P : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
    TaylorGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  | .taylor => P
  | .degree => sphereSobolevShiftedDegreeL (3/2:ℝ)
  | .rotation i j => sphereSobolevRotationL (3/2:ℝ) i j

def taylorGeneratorWeight (r : ℝ) : TaylorGeneratorIndex → ℝ
  | .taylor => r^2
  | .degree => 1
  | .rotation _ _ => 1

def taylorGeneratorCommutator
    (D : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (R : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    TaylorGeneratorIndex → TaylorGeneratorIndex →
      SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  | .taylor,.degree => D
  | .degree,.taylor => -D
  | .taylor,.rotation i j => -R i j
  | .rotation i j,.taylor => R i j
  | .rotation i j,.rotation a b => rotationLieRemainderL (1/2:ℝ) i j a b
  | _,_ => 0

def taylorGeneratorScalarCommutator
    (S : ClosedCoefficientJets 3 → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    TaylorGeneratorIndex → ClosedCoefficientJets 3 →
      SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  | .taylor => S
  | .degree => closedHalfRadialScalarCommutatorL F0 ha0
  | .rotation i j => closedCoefficientAngularHalfL i j

namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma generator_commutator_graph (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (a b : TaylorGeneratorIndex) :
    (taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)) a).comp
      (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)) b)-
    (taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)) b).comp
      (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)) a)=
    (taylorGeneratorCommutator
      (A.domain.degreeFamily h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)).adjoint
      (fun i j => fderiv ℝ s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeAngularTangent d.γ ((y,frameVectorLinear d.frame y),0) i j)) a b).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hD := s.response.adjointTaylor_balanced_degree_commutator A.domain h hK (by norm_num) F0 hF0 p A.domain.pointMem
  have hR := fun i j => s.response.adjointTaylor_balanced_rotation_commutator A.domain h hK
    (by norm_num) F0 hF0 p A.domain.pointMem he i j
  cases a <;> cases b
  · simp only [taylorGeneratorLow,taylorGeneratorHigh,taylorGeneratorCommutator,sub_self,ContinuousLinearMap.zero_comp]
  · simpa only [taylorGeneratorLow,taylorGeneratorHigh,taylorGeneratorCommutator,
      degreeEndpointCommutator,ContinuousLinearMap.neg_comp,neg_sub,neg_neg,p]
      using congrArg Neg.neg hD
  · simpa only [taylorGeneratorLow,taylorGeneratorHigh,taylorGeneratorCommutator,
      ContinuousLinearMap.neg_comp,neg_sub] using congrArg Neg.neg (hR _ _)
  · exact hD
  · simp only [taylorGeneratorLow,taylorGeneratorHigh,taylorGeneratorCommutator,sub_self,ContinuousLinearMap.zero_comp]
  · rename_i i j
    have hh := sphereSobolevShiftedDegreeL_rotation_commute (3/2:ℝ) i j
    have hD' : sphereSobolevShiftedDegreeL ((3/2:ℝ)-1)=sphereSobolevShiftedDegreeL (1/2:ℝ) := by congr 1 <;> norm_num
    have hR' : sphereSobolevRotationL ((3/2:ℝ)-1) i j=sphereSobolevRotationL (1/2:ℝ) i j := by congr 1 <;> norm_num
    rw [hD',hR'] at hh
    exact (sub_eq_zero.mpr hh).trans (ContinuousLinearMap.zero_comp _).symm
  · exact hR _ _
  · rename_i i j
    have hh := sphereSobolevShiftedDegreeL_rotation_commute (3/2:ℝ) i j
    have hD' : sphereSobolevShiftedDegreeL ((3/2:ℝ)-1)=sphereSobolevShiftedDegreeL (1/2:ℝ) := by congr 1 <;> norm_num
    have hR' : sphereSobolevRotationL ((3/2:ℝ)-1) i j=sphereSobolevRotationL (1/2:ℝ) i j := by congr 1 <;> norm_num
    rw [hD',hR'] at hh
    exact (sub_eq_zero.mpr hh.symm).trans (ContinuousLinearMap.zero_comp _).symm
  · rename_i i j a b
    have hh := sphereSobolevRotationL_lie_commutator (3/2:ℝ) i j a b
    have hR' (k l : I) : sphereSobolevRotationL ((3/2:ℝ)-1) k l=sphereSobolevRotationL (1/2:ℝ) k l := by congr 1 <;> norm_num
    have hK' : rotationLieRemainderL ((3/2:ℝ)-1) i j a b=rotationLieRemainderL (1/2:ℝ) i j a b := by congr 1 <;> norm_num
    have hI' : sphereSobolevInclusionL (3/2:ℝ) ((3/2:ℝ)-1) (by norm_num)=sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
    simpa only [hR',hK',hI',taylorGeneratorLow,taylorGeneratorHigh,taylorGeneratorCommutator] using hh

lemma scalar_commutator_graph (A : NativeTaylorGeneratorBounds s h hK C)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (a : TaylorGeneratorIndex) (Q : ClosedCoefficientJets 3) :
    (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)) a).comp
      (closedThreeJetHigherScalarMultiplierL Q)-
    (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp
      (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)) a)=
    (taylorGeneratorScalarCommutator A.scalar F0 ha0 a Q).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  cases a
  · exact A.scalar_graph Q
  · exact degree_closed_scalar_commutator_higher_graph F0 ha0 hFlat hInv0 Q
  · exact rotation_closed_scalar_commutator_higher_graph _ _ Q
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
