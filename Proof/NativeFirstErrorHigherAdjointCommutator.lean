import Proof.NativeFirstErrorHigherAdjointModel
import Proof.NativeFirstErrorHigherPointBounds
import Proof.NativeActualFirstErrorHigherCombination
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
theorem actual_first_error_higher_adjoint_commutator
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
    (Ha Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hHb : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hb=
      (s.firstAdjointErrorFamily Cb ((y,frameVectorLinear d.frame y),0)).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
    let CA := firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR
    let B := firstErrorHigherCommonBudget F0 ha0 Q0 CG CKN CKH BS CQ CI CW K (M 0) CC CR
    GradedHigherEndpointCommutatorBound (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (s.firstAdjointHalfErrorFamily Ca p).adjoint (s.firstAdjointHalfErrorFamily Cb p) Ha Hb
      ((3*C^3*CA^2+6*B^2)*‖a‖*‖b‖*(d.radius y)^2) := by
  have hModel := A.firstErrorHigherAdjointNormalBound G ha0 HS HG hBS hd hK1 hf hε hε1 hy hr1 hCQ hΩ hF0 Q0 hQ0
    hCC Ca Cb CR hCR hRa hRb KN CKN hCKN hKN KH CKH hCKH hKH hP hKern
  exact G.firstErrorHigherNormalBound_physical ha0 Q0 Ca Cb KN _ hF0 hQ0
    (hd.2.2.2.2.1.2 y hy).1 hP Ha Hb hHa hHb hModel
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
