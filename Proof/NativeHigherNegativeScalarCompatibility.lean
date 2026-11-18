import Proof.NativeHigherScalarPointNorm
import Proof.NativeScalarKernelEndpointCompatibility
import Proof.NativeFullAdjointScalarCommutator
import Proof.ClosedHigherScalarMultiplier
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma closedThreeJet_higher_scalar_multiplier_negative (Q : ClosedCoefficientJets 3)
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (closedThreeJetHigherScalarMultiplierL Q u)=
    closedThreeJetNegativeScalarMultiplierL Q
      (sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num) u) := by
  calc
    _ = sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
            (closedThreeJetHigherScalarMultiplierL Q u))) := by
      simp only [sphereSobolevInclusionL_trans_apply]
    _ = _ := by
      rw [closedThreeJet_higher_scalar_multiplier_half,closedThreeJet_half_scalar_multiplier_coarse,
        closedThreeJet_negative_scalar_multiplier_coarse]
      simp only [sphereSobolevInclusionL_trans_apply]

lemma radialCorrectionAdjointSobolevL_high_negative (ell : X →L[ℝ] ℝ)
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (radialCorrectionAdjointSobolevL (3/2:ℝ) ell u)=
    radialCorrectionNegativeAdjointMapL ell
      (sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num) u) := by
  rw [radialCorrectionNegativeAdjointMapL_apply]
  exact sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (3/2:ℝ) (-(1/2:ℝ)) (by norm_num) (radialCorrectionVector ell) u

namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma higherScalarGeneratorFromRotationData_negative_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (a : TaylorGeneratorIndex) (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let IHN := sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    IHN.comp (A.higherScalarGeneratorFromRotationData ha0 a Q R p)=
      (nativeNegativeScalarGeneratorCommutator s ha0 p a (Q p)).comp IHN := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hH := (H.2 CG G Q R hR a).1
  have hN := G.scalar_kernel_half_negative_compatible hF0 ha0
    (fun z hz => hF0 z (unitBall_subset_closedBall_two hz)) a (Q p)
  apply ContinuousLinearMap.ext
  intro u
  have hHu : I1 (A.higherScalarGeneratorFromRotationData ha0 a Q R p u)=
      taylorGeneratorScalarCommutator G.scalar F0 ha0 a (Q p) (I1 u) := DFunLike.congr_fun hH u
  have hNu : I0 (taylorGeneratorScalarCommutator G.scalar F0 ha0 a (Q p) (I1 u))=
      nativeNegativeScalarGeneratorCommutator s ha0 p a (Q p) (I0 (I1 u)) := DFunLike.congr_fun hN (I1 u)
  have hh := (congrArg I0 hHu).trans hNu
  simpa only [I0,I1,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh

def fullAdjointScalarHigherFromRotationData
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  A.higherScalarGeneratorFromRotationData ha0 .taylor Q R p+
    A.higherScalarGeneratorFromRotationData ha0 .degree Q R p+
    d.radius y • ((radialCorrectionAdjointSobolevL (3/2:ℝ) (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
      (closedThreeJetHigherScalarMultiplierL (Q p))-
    (closedThreeJetHigherScalarMultiplierL (Q p)).comp
      (radialCorrectionAdjointSobolevL (3/2:ℝ) (normalFrameRelativeFirstCovector d.γ d.g₁ p)))

lemma fullAdjointScalarHigherFromRotationData_negative_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hR : ∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let IHN := sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    IHN.comp (A.fullAdjointScalarHigherFromRotationData ha0 Q R p)=
      (s.response.fullAdjointScalarCommutator F0 ha0 (Q p) p).comp IHN := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let IHN := sphereSobolevInclusionL (3/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hT := A.higherScalarGeneratorFromRotationData_negative_compatible G ha0 H hF0 .taylor Q R hR
  have hD := A.higherScalarGeneratorFromRotationData_negative_compatible G ha0 H hF0 .degree Q R hR
  have hTu (u : SphereSobolev (3/2:ℝ)) : IHN (A.higherScalarGeneratorFromRotationData ha0 .taylor Q R p u)=
      nativeNegativeScalarGeneratorCommutator s ha0 p .taylor (Q p) (IHN u) := DFunLike.congr_fun hT u
  have hDu (u : SphereSobolev (3/2:ℝ)) : IHN (A.higherScalarGeneratorFromRotationData ha0 .degree Q R p u)=
      nativeNegativeScalarGeneratorCommutator s ha0 p .degree (Q p) (IHN u) := DFunLike.congr_fun hD u
  apply ContinuousLinearMap.ext
  intro u
  change IHN (A.fullAdjointScalarHigherFromRotationData ha0 Q R p u)=
    s.response.fullAdjointScalarCommutator F0 ha0 (Q p) p (IHN u)
  simp only [fullAdjointScalarHigherFromRotationData,NormalFrameRelativeResponsePacket.fullAdjointScalarCommutator,
    ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,_root_.smul_apply,_root_.neg_apply,
    IHN.map_add,IHN.map_sub,IHN.map_smul,hTu,hDu]
  simp only [IHN,radialCorrectionAdjointSobolevL_high_negative,closedThreeJet_higher_scalar_multiplier_negative,
    nativeNegativeScalarGeneratorCommutator,_root_.neg_apply]
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
