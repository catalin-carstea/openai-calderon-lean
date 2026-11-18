import Proof.NativeFirstErrorAdjointRemainderNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Shared actual radial correction bound at the two old endpoints;
    the quadratic estimate is retained for the original self commutator. -/
lemma NativeRelativeHorizontalTaylorData.first_error_radial_endpoint_bounds
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (hCQ : 0 ≤ CQ)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
    let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
    let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
    ‖radialScalarBoundedHalfL ell N‖ ≤ (radialScalarEndpointBudget CQ*C1)*‖a‖*(d.radius y)^2 ∧
    ‖radialScalarBoundedNegativeL ell N‖ ≤ (radialScalarEndpointBudget CQ*C1)*‖a‖*(d.radius y)^2 := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC0 := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hC1 : 0 ≤ C1 := by dsimp only [C1];positivity
  have hEll : ‖ell‖ ≤ CQ := by
    simpa only [norm_iteratedFDeriv_zero] using s.coefficients.firstCovectorJets (by norm_num) 0 (by norm_num)
  have hN := hd.normal_scalar_coefficient_bound hK hf hε hε1 hy hr1 Q0 hCC a C
  obtain ⟨hHalf,hNegative⟩ := norm_radialScalarBounded_endpoints_le CQ hCQ ell hEll N
    (C1*‖a‖*(d.radius y)^2) (by positivity) hN
  exact ⟨hHalf.trans_eq (by ring),hNegative.trans_eq (by ring)⟩

lemma NativeRelativeHorizontalTaylorData.first_error_radial_endpoint_linear_bounds
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (hCQ : 0 ≤ CQ)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
    let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
    let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
    ‖radialScalarBoundedHalfL ell N‖ ≤ (radialScalarEndpointBudget CQ*C1)*‖a‖*(d.radius y) ∧
    ‖radialScalarBoundedNegativeL ell N‖ ≤ (radialScalarEndpointBudget CQ*C1)*‖a‖*(d.radius y) := by
  have hh := s.first_error_radial_endpoint_bounds hd hK hf hε hε1 hy hr1 hCQ Q0 hCC a C
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC0 := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hCZ : 0 ≤ radialScalarEndpointBudget CQ := (radialScalarEndpointBudget_pos CQ).le
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hr2 : (d.radius y)^2 ≤ d.radius y := by nlinarith
  have hScale : 0 ≤ (radialScalarEndpointBudget CQ*
      (firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)))*‖a‖ := by positivity
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left hr2 hScale),hh.2.trans (mul_le_mul_of_nonneg_left hr2 hScale)⟩
end ShrinkingSpheres
