import Proof.ClosedScalarNormalDerivative
import Proof.NativeMultiplierForcingBilinear
import Proof.NativeClosedMultiplierSmoothIdentity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
local instance closedRadialScalarCompleteHalf : CompleteSpace (SphereSobolev (1/2:ℝ)) := lp.completeSpace

def smoothHalfRadialScalarCommutatorL (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    SmoothCoefficientJets 3 →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  let O := (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL).comp
    (strongDirichletOperator fixedSobolevCalculus 0 F).inverse
  let W := nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner
  (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) (BallSobolev 0) (SphereSobolev (1/2:ℝ)) O).comp
    (((ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 (BallSobolev 0)).flip W).comp
      (nativeBulkMultiplierForcingInMultiplierL F))+
        closedScalarNormalDerivativeHalfL.comp (smoothCoefficientClosureInclusionL 3)

lemma smoothHalfRadialScalarCommutatorL_apply (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    smoothHalfRadialScalarCommutatorL F ha Q=halfRadialMultiplierCommutatorL F ha Q := by
  change _+closedScalarNormalDerivativeHalfL (smoothCoefficientClosureInclusionL 3 Q)=_
  rw [closedScalarNormalDerivativeHalfL_on_smooth]
  apply ContinuousLinearMap.ext
  intro f
  rfl

def closedHalfRadialScalarCommutatorL (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    ClosedCoefficientJets 3 →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  (smoothHalfRadialScalarCommutatorL F ha).extend (smoothCoefficientClosureInclusionL 3)

lemma closedHalfRadialScalarCommutatorL_on_smooth (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    closedHalfRadialScalarCommutatorL F ha (smoothCoefficientClosureInclusionL 3 Q)=
      halfRadialMultiplierCommutatorL F ha Q := by
  exact ((smoothHalfRadialScalarCommutatorL F ha).extend_eq (denseRange_smoothCoefficientClosureInclusionL 3)
    (show Isometry (smoothCoefficientClosureInclusionL 3) from fun _ _ => rfl).isUniformInducing Q).trans
      (smoothHalfRadialScalarCommutatorL_apply F ha Q)
end ShrinkingSpheres
