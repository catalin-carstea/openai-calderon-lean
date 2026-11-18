import Proof.GradedHigherEndpointCommutatorBound
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

theorem firstErrorHigherGeneratorBound
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (HS : NativeScalarGeneratorRotationData A ha0 BS) (HG : NativeHigherGeneratorCommutatorData G BG)
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
    :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Qa := signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca)
    let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
    let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
    let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
    let low (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) := ∑ k,(Gl k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q k))
    let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) := ∑ k,(Gh k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
    let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
    let CA := firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR
    GradedHigherEndpointCommutatorBound (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (low Qa) (low Qb) (high Qa) (high Qb)
      ((3*C^3*CA^2)*‖a‖*‖b‖*(d.radius y)^2) := by
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  exact ⟨A.firstErrorHigherGeneratorCommutator G ha0 Q0 Ca Cb ((y,frameVectorLinear d.frame y),0),
    A.firstErrorHigherGeneratorCommutator_graph G ha0 HS hΩ hF0 he hFlat s.point.flatStrong Q0 hQ0 Ca Cb,
    A.firstErrorHigherGeneratorCommutator_norm_le G ha0 HS HG hd hK1 hf hε hε1 hy hr1 Q0 hCC Ca Cb CR hCR hRa hRb⟩
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
