import Proof.NativeScalarHigherEndpoints
import Proof.NativeTaylorGeneratorSystem
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
  {t : NormalFrameRelativeResponsePacket q}

/-- Higher realizations for the SAME response agree through their actual
coarse restrictions, independently of the selected domain witness. -/
lemma SymmetricAdjointDomain.adjointHigherTaylor_eq_on_overlap
    (V W : t.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hpV : p ∈ V.domain) (hpW : p ∈ W.domain) :
    V.adjointHigherTaylor h hK hZ p=W.adjointHigherTaylor h hK hZ p := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  exact (DFunLike.congr_fun (V.adjointHigherTaylor_coarse_compatible h hK hZ F0 hF0 p hpV) u).trans
    (DFunLike.congr_fun (W.adjointHigherTaylor_coarse_compatible h hK hZ F0 hF0 p hpW) u).symm
end NormalFrameRelativeResponsePacket

namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma scalar_eq_selected_generator (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : ClosedCoefficientJets 3) :
    s.response.adjointHalfScalarCommutator F0 A.kernel Q ((y,frameVectorLinear d.frame y),0)=G.scalar Q := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  have hHigh := A.domain.adjointHigherTaylor_eq_on_overlap G.domain h hK (by norm_num) F0 hF0
    _ A.domain.pointMem G.domain.pointMem
  have hh := A.high_graph _ A.pointMem Q
  rw [hHigh] at hh
  exact hh.symm.trans (G.scalar_graph Q)

lemma scalarHigherFamilyFromRotationData_selected_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.scalarHigherFamilyFromRotationData Q R p)=
      (G.scalar (Q p)).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hh := A.scalarHigherFamilyFromRotationData_compatible hΩ hF0 he Q R hR
  dsimp only at hh
  rw [A.scalar_eq_selected_generator G hF0] at hh
  exact hh

lemma scalarHigherFamilyFromRotationData_selected_graph
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (G.domain.adjointHigherTaylor h hK (by norm_num) p).comp (closedThreeJetHigherScalarMultiplierL (Q p))-
      (closedThreeJetHalfBoundaryScalarMultiplierL (Q p)).comp (G.domain.adjointHigherTaylor h hK (by norm_num) p)=
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.scalarHigherFamilyFromRotationData Q R p) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  exact (G.scalar_graph (Q p)).trans
    (A.scalarHigherFamilyFromRotationData_selected_compatible G hΩ hF0 he Q R hR).symm

lemma scalarHigherFamily_selected_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 4) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp (A.scalarHigherFamily Q0 Q p)=
      (G.scalar (closedCoefficientLowerJetsL 3 (Q p))).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact A.scalarHigherFamilyFromRotationData_selected_compatible G hΩ hF0 he
    (fun p => closedCoefficientLowerJetsL 3 (Q p))
    (fun ij p => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 (Q p))
    (fun i j => closedFourJetAngularDerivative_half Q0 hQ0 i j _)
/-- The genuine higher scalar realization is the SAME actual selected
Taylor/scalar commutator, with an explicit order-zero higher endpoint. -/
lemma scalarHigherFamily_selected_graph
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 4) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (G.domain.adjointHigherTaylor h hK (by norm_num) p).comp
        (closedThreeJetHigherScalarMultiplierL (closedCoefficientLowerJetsL 3 (Q p)))-
      (closedThreeJetHalfBoundaryScalarMultiplierL (closedCoefficientLowerJetsL 3 (Q p))).comp
        (G.domain.adjointHigherTaylor h hK (by norm_num) p)=
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.scalarHigherFamily Q0 Q p) := by
  exact A.scalarHigherFamilyFromRotationData_selected_graph G hΩ hF0 he
    (fun p => closedCoefficientLowerJetsL 3 (Q p))
    (fun ij p => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 (Q p))
    (fun i j => closedFourJetAngularDerivative_half Q0 hQ0 i j _)
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
