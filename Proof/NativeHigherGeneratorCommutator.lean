import Proof.HigherTaylorGeneratorCommutator
import Proof.NativeTaylorRotationHigherEndpoints
import Proof.NativeTaylorDegreeHigherData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def higherCommutatorFamily (A : NativeTaylorGeneratorBounds s h hK CG)
    (a b : TaylorGeneratorIndex) (p : NormalFrameRelativeParameter) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  taylorGeneratorHigherCommutator
    (A.domain.adjointDegreeHigherFamily h hK (by norm_num) p)
    (fun i j => A.domain.adjointRotationHigherFamily h hK (by norm_num) i j p) a b

lemma higherCommutatorFamily_compatible (A : NativeTaylorGeneratorBounds s h hK CG)
    (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (a b : TaylorGeneratorIndex) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (A.higherCommutatorFamily a b ((y,frameVectorLinear d.frame y),0))=
    (taylorGeneratorCommutator
      (A.domain.degreeFamily h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)).adjoint
      (fun i j => fderiv ℝ s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeAngularTangent d.γ ((y,frameVectorLinear d.frame y),0) i j)) a b).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  taylorGeneratorHigherCommutator_compatible _ _ _ _
    (A.domain.adjointDegreeHigherFamily_compatible hΩ h hK (by norm_num) _ A.domain.pointMem)
    (fun i j => A.domain.adjointRotationHigherFamily_compatible hΩ h hK (by norm_num)
      F0 hF0 _ A.domain.pointMem he i j) a b

/-- All genuine Taylor/degree/rotation commutators use one selected native
higher family, through the physical inclusion of Sobolev orders. -/
lemma higherCommutatorFamily_graph (A : NativeTaylorGeneratorBounds s h hK CG)
    (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (a b : TaylorGeneratorIndex) :
    (taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)) a).comp
      (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)) b)-
    (taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)) b).comp
      (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)) a)=
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (A.higherCommutatorFamily a b ((y,frameVectorLinear d.frame y),0)) :=
  (A.generator_commutator_graph hF0 he a b).trans
    (A.higherCommutatorFamily_compatible hΩ hF0 he a b).symm

lemma higherCommutatorFamily_jets (A : NativeTaylorGeneratorBounds s h hK CG)
    (B : ℝ) (hB : 0 ≤ B) (hRot : 4*Real.sqrt 2 ≤ B)
    (hD : SmoothFiniteJetBound (A.domain.adjointDegreeHigherFamily h hK (by norm_num))
      ((y,frameVectorLinear d.frame y),0) 2 (B*(d.radius y)^2))
    (hR : ∀ i j,SmoothFiniteJetBound (A.domain.adjointRotationHigherFamily h hK (by norm_num) i j)
      ((y,frameVectorLinear d.frame y),0) 2 (B*(d.radius y)^2))
    (a b : TaylorGeneratorIndex) :
    SmoothFiniteJetBound (A.higherCommutatorFamily a b) ((y,frameVectorLinear d.frame y),0) 2
      (B*(taylorGeneratorWeight (d.radius y) a*taylorGeneratorWeight (d.radius y) b)) :=
  taylorGeneratorHigherCommutator_jets _ _ _ _ _ _ hB hRot hD hR a b
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
