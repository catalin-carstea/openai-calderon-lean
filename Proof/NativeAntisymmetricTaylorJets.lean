import Proof.NativeNormalCommutatorExpansion
import Proof.NativeAntisymmetricTaylorGraph
import Proof.CompletedNormalMultiplierJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
local instance nativeAntiCompleteNegative : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := lp.completeSpace

def nativeAntisymmetricTaylorJetBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 2) (CQ CI CW CR : ℝ) : ℝ :=
  let BQ := ‖smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q)‖+‖linearScalarClosedCoefficientL Q‖*CQ+CR
  let BM := ‖closedThreeJetNegativeScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*CQ+CR)
  let BI := 2*((Nat.factorial 3:ℝ)*(Nat.factorial 3:ℝ)*(1+2*(‖closedThreeJetNegativeScalarMultiplierL‖*BQ))^3)
  let BC := ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖*(‖linearScalarClosedCoefficientL Q‖*CQ)
  let BR := (2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)*BQ)+
    ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖*CR+2*(2^3)*‖radialCorrectionNegativeAdjointMapL‖*CQ*BM
  (2^3*(2^3*BI*BM)*BC+2^3*BI*BR)

lemma NativeRelativeHorizontalTaylorData.antisymmetricTaylor_three_jets
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM CR : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (R : RelativeNormalScalarRemainderFamily d y CR) (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCR : 0 ≤ CR)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hNear : (‖closedThreeJetNegativeScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*CQ+CR))*d.radius y ≤ (1/2:ℝ)) :
    SmoothFiniteJetBound (fun p => s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q p)
      (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p)
      ((y,frameVectorLinear d.frame y),0) 3 (nativeAntisymmetricTaylorJetBudget F0 ha0 Q CQ CI CW CR*(d.radius y)^2) := by
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let BQ := ‖smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q)‖+‖linearScalarClosedCoefficientL Q‖*CQ+CR
  let BM := ‖closedThreeJetNegativeScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*CQ+CR)
  let BI := 2*((Nat.factorial 3:ℝ)*(Nat.factorial 3:ℝ)*(1+2*(‖closedThreeJetNegativeScalarMultiplierL‖*BQ))^3)
  let BC := ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖*(‖linearScalarClosedCoefficientL Q‖*CQ)
  let BR := (2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)*BQ)+
    ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖*CR+2*(2^3)*‖radialCorrectionNegativeAdjointMapL‖*CQ*BM
  have hEll : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁) p0 3 CQ :=
    ⟨hCQ,s.coefficients.covectorSmooth.contDiffAt (s.coefficients.domainOpen.mem_nhds s.coefficients.pointMem),
      fun n hn => s.coefficients.firstCovectorJets (by norm_num) n (by omega)⟩
  have hN : SmoothFiniteJetBound (R.normalCoefficient Q) p0 3 BQ := R.normalCoefficient_three_jets Q hCR hr hr1 hEll
  have hM := hN.clm closedThreeJetNegativeScalarMultiplierL
  have hSmall : SmoothFiniteJetBound (fun p => closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)-
      ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) p0 3 (BM*d.radius y) :=
    R.normalNegative_small_three_jets Q hQ hCR hr hr1 hEll
  have hAt : ‖closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p0)-
      ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ (1/2:ℝ) :=
    by
      have hAt0 : ‖closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p0)-
          ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ BM*d.radius y := by
        simpa only [norm_iteratedFDeriv_zero] using hSmall.bound 0 (by norm_num)
      exact hAt0.trans hNear
  obtain ⟨hInv,hInvBound⟩ := near_identity_inverse_data _ hAt
  have hI : SmoothFiniteJetBound (fun p => (closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)).inverse) p0 3 BI :=
    hM.inverse hInv (by norm_num) hInvBound
  have hCell := (hEll.clm (linearScalarClosedCoefficientL Q)).clm (closedNegativeDegreeScalarCommutatorL F0 ha0)
  have hRest : SmoothFiniteJetBound (s.scalarCommutatorRest ha0 (R.normalCoefficient Q) R.closed) p0 3 (BR*(d.radius y)^2) :=
    s.scalarCommutatorRest_three_jets ha0 hF0 hCQ hCI hCW hr hr1 _ _ BQ CR BM CQ hN R.jets hSmall hEll
  have hCancel := conjugation_taylor_cancellation_finite_jets
    (fun p => closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p))
    (fun p => closedNegativeDegreeScalarCommutatorL F0 ha0
      (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)))
    (s.scalarCommutatorRest ha0 (R.normalCoefficient Q) R.closed) p0 3 (d.radius y) BI BM BC BR
    hM.smooth hInv hr hI hSmall hCell hRest
  apply hCancel.congr_germ
  exact Filter.Eventually.of_forall (fun p => congrArg
    (fun T : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      -(closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)).inverse.comp T+
        d.radius y • closedNegativeDegreeScalarCommutatorL F0 ha0
          (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)))
    (s.fullAdjoint_normal_scalar_commutator_expansion ha0 hF0 R Q hQ p).symm)
end ShrinkingSpheres
