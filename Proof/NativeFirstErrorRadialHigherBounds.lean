import Proof.RadialScalarHigherEndpoints
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

def radialScalarHigherCommonBudget : ℝ :=
  6*(radialDriftSobolevBound (-(3/2:ℝ))+radialDriftSobolevBound (3/2:ℝ))*
    ‖closedThreeJetHigherScalarMultiplierL‖

lemma radialScalarHigherCommonBudget_nonneg : 0 ≤ radialScalarHigherCommonBudget := by
  have hF : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hA : 0 ≤ radialDriftSobolevBound (3/2:ℝ) := zero_le_one.trans (le_max_left _ _)
  unfold radialScalarHigherCommonBudget
  positivity

lemma NativeRelativeHorizontalTaylorData.first_error_radial_higher_bounds
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
    ‖radialScalarBoundedHigherL ell N‖ ≤
      (radialScalarHigherCommonBudget*CQ*C1)*‖a‖*(d.radius y) ∧
    ‖radialScalarBoundedAdjointHigherL ell N‖ ≤
      (radialScalarHigherCommonBudget*CQ*C1)*‖a‖*(d.radius y) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
  let CZ := radialScalarHigherCommonBudget
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC0 := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hC1 : 0 ≤ C1 := by dsimp only [C1];positivity
  have hCZ : 0 ≤ CZ := radialScalarHigherCommonBudget_nonneg
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hr2 : (d.radius y)^2 ≤ d.radius y := by nlinarith
  have hEll : ‖ell‖ ≤ CQ := by
    simpa only [norm_iteratedFDeriv_zero] using s.coefficients.firstCovectorJets (by norm_num) 0 (by norm_num)
  have hN := hd.normal_scalar_coefficient_bound hK hf hε hε1 hy hr1 Q0 hCC a C
  have hBound (Z : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
      (hZ : ‖Z‖ ≤ CZ*‖ell‖*‖N‖) : ‖Z‖ ≤ (CZ*CQ*C1)*‖a‖*(d.radius y) := by
    have hZN := hZ.trans (mul_le_mul (mul_le_mul_of_nonneg_left hEll hCZ) hN (norm_nonneg _) (mul_nonneg hCZ hCQ))
    exact hZN.trans ((by ring : CZ*CQ*(C1*‖a‖*(d.radius y)^2)=(CZ*CQ*C1*‖a‖)*(d.radius y)^2).le.trans
      (mul_le_mul_of_nonneg_left hr2 (by positivity)))
  have hF : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hA : 0 ≤ radialDriftSobolevBound (3/2:ℝ) := zero_le_one.trans (le_max_left _ _)
  have hCF : 6*radialDriftSobolevBound (-(3/2:ℝ))*‖closedThreeJetHigherScalarMultiplierL‖ ≤ CZ := by
    dsimp only [CZ,radialScalarHigherCommonBudget]
    nlinarith only [mul_nonneg hA (norm_nonneg closedThreeJetHigherScalarMultiplierL)]
  have hCA : 6*radialDriftSobolevBound (3/2:ℝ)*‖closedThreeJetHigherScalarMultiplierL‖ ≤ CZ := by
    dsimp only [CZ,radialScalarHigherCommonBudget]
    nlinarith only [mul_nonneg hF (norm_nonneg closedThreeJetHigherScalarMultiplierL)]
  exact ⟨hBound _ ((norm_radialScalarBoundedHigherL_le ell N).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCF (norm_nonneg ell)) (norm_nonneg N))),
    hBound _ ((norm_radialScalarBoundedAdjointHigherL_le ell N).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA (norm_nonneg ell)) (norm_nonneg N)))⟩
end ShrinkingSpheres
