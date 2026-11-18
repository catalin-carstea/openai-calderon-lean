import Proof.NativeFullAdjointScalarCommutator
import Proof.NativeScalarMultiplierKernelJets
import Proof.ConjugationCancellationFiniteJets
import Proof.CompletedNormalCoefficientJets
import Proof.ClosedScalarIdentity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}
namespace NativeRelativeHorizontalTaylorData

def scalarCommutatorRest (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Qn Qr : NormalFrameRelativeParameter → ClosedCoefficientJets 3) (p : NormalFrameRelativeParameter) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  -(s.coefficients.scalarMultiplierKernel F0 (Qn p) p).adjoint+
    closedNegativeDegreeScalarCommutatorL F0 ha0 (Qr p)+d.radius y •
      ((radialCorrectionNegativeAdjointMapL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
        (closedThreeJetNegativeScalarMultiplierL (Qn p)-ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ))))-
       (closedThreeJetNegativeScalarMultiplierL (Qn p)-ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))).comp
        (radialCorrectionNegativeAdjointMapL (normalFrameRelativeFirstCovector d.γ d.g₁ p)))

lemma scalarCommutatorRest_three_jets
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (Qn Qr : NormalFrameRelativeParameter → ClosedCoefficientJets 3) (BQ BR BM BL : ℝ)
    (hQ : SmoothFiniteJetBound Qn ((y,frameVectorLinear d.frame y),0) 3 BQ)
    (hR : SmoothFiniteJetBound Qr ((y,frameVectorLinear d.frame y),0) 3 (BR*(d.radius y)^2))
    (hM : SmoothFiniteJetBound (fun p => closedThreeJetNegativeScalarMultiplierL (Qn p)-
      ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) ((y,frameVectorLinear d.frame y),0) 3 (BM*d.radius y))
    (hL : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁)
      ((y,frameVectorLinear d.frame y),0) 3 BL) :
    SmoothFiniteJetBound (s.scalarCommutatorRest ha0 Qn Qr) ((y,frameVectorLinear d.frame y),0) 3
      (((2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)*BQ)+
        ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖*BR+
          2*(2^3)*‖radialCorrectionNegativeAdjointMapL‖*BL*BM)*(d.radius y)^2) := by
  have hK := (s.scalarMultiplierKernel_three_jets hF0 hCQ hCI hCW hr hr1 Qn BQ hQ).adjoint.neg
  have hD := hR.clm (closedNegativeDegreeScalarCommutatorL F0 ha0)
  have hB := hL.clm radialCorrectionNegativeAdjointMapL
  have hC := ((hB.comp hM).sub (hM.comp hB)).const_smul (d.radius y)
  rw [abs_of_nonneg hr] at hC
  have hAll := (hK.add hD).add hC
  have hBudget : ((2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)*BQ)*(d.radius y)^2+
      ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖*(BR*(d.radius y)^2))+
      d.radius y*(2^3*(‖radialCorrectionNegativeAdjointMapL‖*BL)*(BM*d.radius y)+
        2^3*(BM*d.radius y)*(‖radialCorrectionNegativeAdjointMapL‖*BL))=
      ((2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)*BQ)+
        ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖*BR+
          2*(2^3)*‖radialCorrectionNegativeAdjointMapL‖*BL*BM)*(d.radius y)^2 := by ring
  exact hAll.weaken (le_of_eq hBudget)
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
