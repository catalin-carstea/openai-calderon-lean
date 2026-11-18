import Proof.NativeHigherScalarAdjointRemainderData
import Proof.NativeFirstErrorRadialHigherBounds
import Proof.NativeFirstErrorAdjointEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def firstErrorAdjointRemainderHigher
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) {a : X} {CC CH : ℝ}
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  A.scalarAdjointRemainderHigher ha0 KH (actualFirstErrorGeneratorCoefficients Q0 C)
    (fun b ij => actualFirstErrorAngularCoefficients Q0 C ij.1 ij.2 b)+
  radialScalarBoundedAdjointHigherL (normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0))
    (∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed ((y,frameVectorLinear d.frame y),0)))

lemma firstErrorAdjointRemainderHigher_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {a : X} {CC CH : ℝ} (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hKern : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.firstErrorAdjointRemainderHigher ha0 Q0 C KH)=
      (G.firstErrorAdjointRemainderHalfL ha0 Q0 C KN).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hS := A.scalarAdjointRemainderHigher_compatible G ha0 H KH KN (actualFirstErrorGeneratorCoefficients Q0 C)
    (fun b ij => actualFirstErrorAngularCoefficients Q0 C ij.1 ij.2 b)
    (fun b i j => actualFirstErrorAngularCoefficients_half Q0 hQ0 C he i j b) hKern
  have hZ := radialScalarBoundedAdjointHigherL_compatible
    (normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0))
    (∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed ((y,frameVectorLinear d.frame y),0)))
  exact (ContinuousLinearMap.comp_add _ _ _).trans
    ((congrArg₂ (fun U V : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => U+V) hS hZ).trans
      (ContinuousLinearMap.add_comp _ _ _).symm)

lemma firstErrorAdjointRemainderHigher_norm_le
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS) (hBS : 0 ≤ BS)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (hCQ : 0 ≤ CQ)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) (BK : ℝ) (hBK : 0 ≤ BK)
    (hKH : ‖KH‖ ≤ BK*(d.radius y)^2)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hR : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient C k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖a‖*(d.radius y)^2) :
    let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
    let CAug := firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR
    let CZ := radialScalarHigherCommonBudget
    ‖A.firstErrorAdjointRemainderHigher ha0 Q0 C KH‖ ≤
      ((‖closedThreeJetHigherScalarMultiplierL‖*BK+BS)*CAug+CZ*CQ*C1)*‖a‖*(d.radius y) := by
  have hRadial := s.first_error_radial_higher_bounds hd hK1 hf hε hε1 hy hr1 hCQ Q0 hCC a C
  have hS := A.actualFirstErrorScalarAdjointRemainderHigher_norm_le ha0 H hBS hd hK1 hf hε hε1 hy hr1
    KH BK hBK hKH Q0 hCC a C CR hCR hR
  exact (norm_add_le _ _).trans ((add_le_add hS hRadial.2).trans_eq (by ring))
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
