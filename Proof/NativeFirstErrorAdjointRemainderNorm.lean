import Proof.NativeFirstErrorAdjointNormalForm
import Proof.NativeTaylorScalarAdjointRemainderBound
import Proof.RadialScalarEndpointBounds
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

def nativeFirstErrorAdjointRemainderL {Y Ω : Set X} {d : Data} {y a : X}
    {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  taylorScalarAdjointRemainderL KN (fun k => nativeNegativeScalarGeneratorCommutator s ha0 p k (Q k)) Q+
    (radialScalarBoundedHalfL (normalFrameRelativeFirstCovector d.γ d.g₁ p)
      (∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Ca j).closed p))).adjoint

/-- The complete displayed adjoint correction, including the radial term,
has a uniform one-radius gain on the negative Sobolev endpoint. -/
lemma NativeRelativeHorizontalTaylorData.norm_first_error_adjoint_remainder
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
    let CR := ‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW
    let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
    ‖nativeFirstErrorAdjointRemainderL s ha0 Q0 Ca KN‖ ≤
      ((CR+radialScalarEndpointBudget CQ)*C1)*‖a‖*(d.radius y) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Ca j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let CR := ‖closedThreeJetNegativeScalarMultiplierL‖*CK+nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  let CZ := radialScalarEndpointBudget CQ
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1) (by positivity)
  have hEll : ‖ell‖ ≤ CQ := by
    have hh := s.coefficients.firstCovectorJets (by norm_num) 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh
  have hN := hd.normal_scalar_coefficient_bound hK hf hε hε1 hy hr1 Q0 hCC a Ca
  have hB : 0 ≤ C1*‖a‖*(d.radius y)^2 := mul_nonneg (mul_nonneg hC1 (norm_nonneg _)) (sq_nonneg _)
  have hZ := (norm_radialScalarBounded_endpoints_le CQ hCQ ell hEll N (C1*‖a‖*(d.radius y)^2) hB hN).1
  have hr2 : (d.radius y)^2 ≤ d.radius y := by nlinarith
  have hZr : ‖(radialScalarBoundedHalfL ell N).adjoint‖ ≤ (CZ*C1)*‖a‖*(d.radius y) := by
    rw [LinearIsometryEquiv.norm_map]
    calc
      _ ≤ CZ*(C1*‖a‖*(d.radius y)^2) := hZ
      _ = (CZ*C1*‖a‖)*(d.radius y)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr2
        (mul_nonneg (mul_nonneg (radialScalarEndpointBudget_pos CQ).le hC1) (norm_nonneg a))
  have hR := s.actual_first_error_adjoint_remainder_bound hd hK hf hε hε1 hy hr1 hF0 ha0
    hCQ hCI hCW KN CK hCK hKN Q0 hCC a Ca
  exact (norm_add_le _ _).trans ((add_le_add hR hZr).trans_eq (by ring))
end ShrinkingSpheres
