import Proof.TaylorScalarAdjointRemainderBound
import Proof.ActualFirstErrorGeneratorCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma NativeRelativeHorizontalTaylorData.native_scalar_adjoint_remainder_bound
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    ‖taylorScalarAdjointRemainderL KN (fun a => nativeNegativeScalarGeneratorCommutator s ha0 p a (Q a)) Q‖ ≤
      (‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW)*
        (∑ a,taylorGeneratorWeight (d.radius y) a*‖Q a‖) := by
  exact norm_taylorScalarAdjointRemainderL_weighted KN _ Q CK _ (d.radius y) hCK hKN
    (fun a => s.negative_scalar_generator_weight_bound hF0 ha0 hCQ hCI hCW hr hr1 a (Q a))

/-- The scalar adjoint reordering correction for the SAME actual first-error
coefficients is bounded by a uniform constant times radius times direction.
This is a one-radius gain; the full radial error term is still separate. -/
lemma NativeRelativeHorizontalTaylorData.actual_first_error_adjoint_remainder_bound
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
    let CR := ‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW
    let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
    ‖taylorScalarAdjointRemainderL KN (fun k => nativeNegativeScalarGeneratorCommutator s ha0 p k (Q k)) Q‖ ≤
      (CR*C1)*‖a‖*(d.radius y) := by
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  let CR := ‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW
  have hCN : 0 ≤ nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW :=
    add_nonneg (zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 _).1) (norm_nonneg _)
  have hCR : 0 ≤ CR := add_nonneg (mul_nonneg (norm_nonneg _) hCK) hCN
  have hR := s.native_scalar_adjoint_remainder_bound hF0 ha0 hCQ hCI hCW
    (hd.2.2.2.2.1.2 y hy).1.le hr1 KN CK hCK hKN Q
  have hQ := hd.first_error_scalar_coefficient_bound hK hf hε hε1 hy hr1 Q0 hCC a Ca
  exact hR.trans ((mul_le_mul_of_nonneg_left hQ hCR).trans_eq (by ring))
end ShrinkingSpheres
