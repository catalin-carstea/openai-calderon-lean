import Proof.NativeAngularHigherScalarGraph
import Proof.GradedScalarRotationJacobi
import Proof.LowScalarGeneratorCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma scalar_rotation_graph_of_angular_coefficient
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q QR : ClosedCoefficientJets 3) (i j : I)
    (hQR : closedThreeJetHalfBoundaryScalarMultiplierL QR=closedCoefficientAngularHalfL i j Q)
    (u : SphereSobolev (3/2:ℝ)) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let C := fun q => s.response.adjointHalfScalarCommutator F0 A.kernel Q q
    let D := normalFrameRelativeAngularDerivative d.γ C i j p+
      s.response.adjointHalfScalarCommutator F0 A.kernel QR p
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (C p (sphereSobolevRotationL (3/2:ℝ) i j u)+
        D (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=
      sphereSobolevRotationL (1/2:ℝ) i j
        (C p (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Ph := A.domain.adjointHigherTaylor h hK (by norm_num) p
  let Pl := s.response.adjointHalfTaylor p
  let Rh := A.domain.adjointRotationHigherFamily h hK (by norm_num) i j p
  let C := s.response.adjointHalfScalarCommutator F0 A.kernel Q p
  let Cd := normalFrameRelativeAngularDerivative d.γ
    (fun q => s.response.adjointHalfScalarCommutator F0 A.kernel Q q) i j p
  let Cr := s.response.adjointHalfScalarCommutator F0 A.kernel QR p
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hPair : I0.comp Ph=Pl.comp I1 :=
    balanced_endpoint_pair_of_coarse _ _ _
      (A.domain.adjointHalfTaylor_coarse_compatible (by norm_num) F0 hF0 p A.domain.pointMem)
      (A.domain.adjointHigherTaylor_coarse_compatible h hK (by norm_num) F0 hF0 p A.domain.pointMem)
  have hC := A.high_graph p A.pointMem Q
  have hClow := balanced_low_scalar_commutator Pl Ph C Q hPair hC
  have hCr := balanced_low_scalar_commutator Pl Ph Cr QR hPair (A.high_graph p A.pointMem QR)
  have hRotPair : I0.comp (sphereSobolevRotationL (3/2:ℝ) i j)=
      (sphereSobolevRotationL (1/2:ℝ) i j).comp I1 :=
    balanced_endpoint_pair_of_coarse _ _ _
      (ContinuousLinearMap.ext (fun v => oneRotation_half_inclusion i j v))
      (sphereSobolevRotationL_threehalf_coarse i j)
  have hQhigh := rotation_closed_scalar_commutator_higher_graph i j Q
  rw [← hQR] at hQhigh
  have hQlow := balanced_low_scalar_commutator _ _ _ Q hRotPair hQhigh
  exact graded_scalar_rotation_jacobi I1 I0 Ph Rh (sphereSobolevRotationL (3/2:ℝ) i j)
    Pl (sphereSobolevRotationL (1/2:ℝ) i j)
    (closedThreeJetHigherScalarMultiplierL Q) (closedThreeJetHalfBoundaryScalarMultiplierL Q)
    (closedThreeJetHalfBoundaryScalarMultiplierL QR) C Cd Cr
    (closedThreeJetNegativeScalarMultiplierL Q) (closedThreeJetNegativeScalarMultiplierL QR)
    hPair (ContinuousLinearMap.ext (fun v => (closedThreeJet_half_negative_scalar_multiplier Q v).symm))
    (ContinuousLinearMap.ext (fun v => (closedThreeJet_half_negative_scalar_multiplier QR v).symm))
    hC hClow
    (A.domain.adjointRotationHigherFamily_graph hΩ h hK (by norm_num) F0 hF0 p A.domain.pointMem he i j)
    hQhigh hQlow (A.angularHigherTaylor_scalar_graph hΩ he Q i j) hCr u
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
