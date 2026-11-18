import Proof.NativeFirstErrorAdjointCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Named exact point data for common uniform mixed adjoint transport. -/
def NativeFirstErrorAdjointCommutatorData {Y Ω : Set X} {d : Data} {y : X}
    {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (CC CH CS : ℝ) : Prop :=
  (∀ a : X,∀ Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH,
        ∃ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
          (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint.comp
            (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) ∧
      ∀ a b : X,
      ∀ Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH,
      ∀ Cb : (j : I) → RelativeCenterErrorCoefficientFamily d y b j CC CH,
      ∀ Ha Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
        (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint.comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hb=
        (s.firstAdjointErrorFamily Cb ((y,frameVectorLinear d.frame y),0)).comp
          (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) →
      GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
        (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint
        (s.firstAdjointHalfErrorFamily Cb ((y,frameVectorLinear d.frame y),0)) Ha Hb
        (CS*‖a‖*‖b‖*(d.radius y)^2)

namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma actual_first_error_adjoint_commutator_data (A : NativeTaylorGeneratorBounds s h hK CG)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {CC CH : ℝ} (hCC : 0 ≤ CC)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
    let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CK CQ CI CW K (M 0) CC
    NativeFirstErrorAdjointCommutatorData s CC CH (3*C0^3*C1^2+6*CP^2) := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  constructor
  · intro a Ca
    exact ⟨A.firstErrorAdjointHigherL ha0 Q0 Ca KN,
      A.first_error_adjoint_balanced_pair hF0 ha0 hFlat Q0 hQ0 Ca hr KN hP⟩
  · intro a b Ca Cb Ha Hb hHa hHb
    exact A.actual_first_error_adjoint_commutator hd hK1 hf hε hε1 hy hr1 hCQ hCI hCW hF0 ha0 hFlat
      Q0 hQ0 hCC a b Ca Cb KN CK hCK hKN hP Ha Hb hHa hHb
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
