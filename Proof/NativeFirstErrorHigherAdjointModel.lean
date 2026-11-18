import Proof.NativeFirstErrorHigherNormalForm
import Proof.NativeFirstErrorHigherPointBounds
import Proof.NativeFirstErrorHigherGeneratorBound
import Proof.NativeFirstErrorAdjointNormalForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS BG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- Complete actual first-error adjoint commutator, with one genuine
    higher witness and its quadratic radius bound, for any physical endpoints. -/
theorem firstErrorHigherAdjointNormalBound
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (HS : NativeScalarGeneratorRotationData A ha0 BS) (HG : NativeHigherGeneratorCommutatorData G BG) (hBS : 0 ≤ BS)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (hCQ : 0 ≤ CQ)
    (hΩ : IsOpen Ω) (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {a b : X} {CC CH : ℝ} (hCC : 0 ≤ CC)
    (Ca : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Cb : (k : I) → RelativeCenterErrorCoefficientFamily d y b k CC CH)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hRa : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient Ca k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖a‖*(d.radius y)^2)
    (hRb : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient Cb k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖b‖*(d.radius y)^2)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (CKN : ℝ) (hCKN : 0 ≤ CKN)
    (hKN : ‖KN‖ ≤ CKN*(d.radius y)^2)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) (CKH : ℝ) (hCKH : 0 ≤ CKH)
    (hKH : ‖KH‖ ≤ CKH*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (hKern : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
 :
    let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
    let CA := firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR
    let B := firstErrorHigherCommonBudget F0 ha0 Q0 CG CKN CKH BS CQ CI CW K (M 0) CC CR
    G.firstErrorHigherNormalBound ha0 Q0 Ca Cb KN ((3*C^3*CA^2+6*B^2)*‖a‖*‖b‖*(d.radius y)^2) := by

  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Qa := signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca)
  let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
  let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
  let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
  let low (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) := ∑ k,(Gl k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q k))
  let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) := ∑ k,(Gh k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let Nb := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cb j).closed p)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Rp := G.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN
  let Rn := nativeFirstErrorAdjointRemainderL s ha0 Q0 Ca KN
  let Rh := A.firstErrorAdjointRemainderHigher ha0 Q0 Ca KH
  let Zp := radialScalarBoundedHalfL ell Nb
  let Zn := radialScalarBoundedNegativeL ell Nb
  let Zh := radialScalarBoundedHigherL ell Nb
  let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
  let CA := firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR
  let B := firstErrorHigherCommonBudget F0 ha0 Q0 CG CKN CKH BS CQ CI CW K (M 0) CC CR
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hGen := A.firstErrorHigherGeneratorBound G ha0 HS HG hd hK1 hf hε hε1 hy hr1 hCQ
    hΩ hF0 Q0 hQ0 hCC Ca Cb CR hCR hRa hRb
  have hA := A.firstErrorHigherPointBounds G ha0 HS hBS hd hK1 hf hε hε1 hy hr1 hCQ
    KN CKN hCKN hKN KH CKH hCKH hKH Q0 hCC a Ca CR hCR hRa
  have hBdir := A.firstErrorHigherPointBounds G ha0 HS hBS hd hK1 hf hε hε1 hy hr1 hCQ
    KN CKN hCKN hKN KH CKH hCKH hKH Q0 hCC b Cb CR hCR hRb
  have hB : 0 ≤ B := zero_le_one.trans (firstErrorHigherCommonBudget_bounds F0 ha0 Q0 CG CKN CKH BS CQ CI CW K (M 0) CC CR).1
  have hFull := hGen.add_bounded_linear I1 Rp Zp Rn Zn Rh Zh
    (G.scalar_combination_balanced_pair hF0 Qa) (G.scalar_combination_balanced_pair hF0 Qb)
    (G.first_error_adjoint_remainder_half_negative_compatible hF0 ha0 hFlat Q0 Ca KN hP)
    (radialScalarBounded_half_negative_compatible ell Nb)
    (A.firstErrorAdjointRemainderHigher_compatible G ha0 HS Q0 hQ0 Ca he KH KN hKern)
    (radialScalarBoundedHigherL_compatible ell Nb)
    B ‖a‖ ‖b‖ (d.radius y) hB (norm_nonneg _) (norm_nonneg _) hr.le (norm_sphereSobolevInclusionL_le _ _ _)
    hA.2.1 hBdir.1 hA.2.2.2.1 hBdir.2.2.2.2.2 hA.2.2.1 hBdir.2.2.2.2.1
  exact hFull.factor_radius_bound

end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
