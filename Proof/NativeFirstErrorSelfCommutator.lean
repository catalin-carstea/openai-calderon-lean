import Proof.GradedEndpointRestrictionTransport
import Proof.NativeFirstErrorRadialBounds
import Proof.NativeFirstErrorScalarEndpoints
import Proof.GradedEndpointCommutatorBound
import Proof.RadialScalarEndpointBounds
import Proof.TaylorScalarLowNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- Genuine first-order self commutator of the complete native first error,
including its bounded radial correction, for ANY SAME compatible higher endpoints.
The constant depends only on the previously produced common budgets. -/
private theorem actual_first_error_self_model_bound (A : NativeTaylorGeneratorBounds s h hK C)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (hCQ : 0 ≤ CQ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {CC CH : ℝ} (hCC : 0 ≤ CC) (a b : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Cb : (j : I) → RelativeCenterErrorCoefficientFamily d y b j CC CH)
 :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let r := d.radius y
    let CB := taylorGeneratorFixedBudget F0 ha0 C
    let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
    let CZ := radialScalarEndpointBudget CQ
    let CP := 1+CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1+CZ*C1
    let coeff (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := actualFirstErrorGeneratorCoefficients Q0 Cu
    let low (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
      ∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (coeff u Cu k))
    let high (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
      ∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp (closedThreeJetHigherScalarMultiplierL (coeff u Cu k))
    let normal (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
      ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cu j).closed p)
    let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
    let zm (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := radialScalarBoundedHalfL ell (normal u Cu)
    let zn (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := radialScalarBoundedNegativeL ell (normal u Cu)
    let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    GradedEndpointCommutatorBound I1 (low a Ca+(zn a Ca).comp I0) (low b Cb+(zn b Cb).comp I0)
      (high a Ca+(zm a Ca).comp I1) (high b Cb+(zm b Cb).comp I1)
      ((3*C0^3*C1^2+6*CP^2)*‖a‖*‖b‖*r^2) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let r := d.radius y
  let CB := taylorGeneratorFixedBudget F0 ha0 C
  let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  let CZ := radialScalarEndpointBudget CQ
  let CP := 1+CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1+CZ*C1
  let coeff (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := actualFirstErrorGeneratorCoefficients Q0 Cu
  let low (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
    ∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (coeff u Cu k))
  let high (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
    ∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp (closedThreeJetHigherScalarMultiplierL (coeff u Cu k))
  let normal (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
    ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cu j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let zm (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := radialScalarBoundedHalfL ell (normal u Cu)
  let zn (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := radialScalarBoundedNegativeL ell (normal u Cu)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hCB : 0 ≤ CB := zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 C).1
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1) (by positivity)
  have hCZ : 0 ≤ CZ := (radialScalarEndpointBudget_pos CQ).le
  have hP0 : 0 ≤ CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1 := by positivity
  have hZ0 : 0 ≤ CZ*C1 := mul_nonneg hCZ hC1
  have hCP : 0 ≤ CP := by dsimp only [CP];linarith only [hP0,hZ0]
  have hPC : CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1 ≤ CP := by dsimp only [CP];linarith only [hZ0]
  have hZC : CZ*C1 ≤ CP := by dsimp only [CP];linarith only [hP0]
  have hEll : ‖ell‖ ≤ CQ := by
    have hh := s.coefficients.firstCovectorJets (by norm_num) 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh
  have hLow (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :
      ‖low u Cu‖ ≤ CP*‖u‖*r := by
    have hQ := hd.first_error_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC u Cu
    calc
      _ ≤ (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*(∑ k,taylorGeneratorWeight r k*‖coeff u Cu k‖) := A.scalar_low_combination_norm ha0 (coeff u Cu)
      _ ≤ (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*(C1*‖u‖*r) := mul_le_mul_of_nonneg_left hQ (mul_nonneg hCB (norm_nonneg _))
      _ = (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1)*‖u‖*r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPC (norm_nonneg _)) hr.le
  have hZ (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :
      ‖zm u Cu‖ ≤ CP*‖u‖*r^2 ∧ ‖zn u Cu‖ ≤ CP*‖u‖*r^2 := by
    obtain ⟨hM,hN'⟩ := s.first_error_radial_endpoint_bounds hd hK1 hf hε hε1 hy hr1 hCQ Q0 hCC u Cu
    have hBudget : (CZ*C1)*‖u‖*r^2 ≤ CP*‖u‖*r^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZC (norm_nonneg _)) (sq_nonneg _)
    exact ⟨hM.trans hBudget,hN'.trans hBudget⟩
  have hGen := (A.actual_first_error_generator_commutator hd hK1 hf hε hε1 hy hr1 hF0 ha0 hFlat hInv0 Q0 hCC a b Ca Cb).graded_bound
  have hFull := hGen.add_bounded I0 (zm a Ca) (zm b Cb) (zn a Ca) (zn b Cb)
    (A.scalar_combination_balanced_pair hF0 (coeff a Ca)) (A.scalar_combination_balanced_pair hF0 (coeff b Cb))
    CP ‖a‖ ‖b‖ r hCP (norm_nonneg _) (norm_nonneg _) hr.le hr1
    (norm_sphereSobolevInclusionL_le _ _ _) (hLow a Ca) (hLow b Cb)
    (hZ a Ca).1 (hZ b Cb).1 (hZ a Ca).2 (hZ b Cb).2
  have hFull' := hFull.mono (le_of_eq (by ring :
    (3*C0^3*C1^2)*‖a‖*‖b‖*r^2+6*CP^2*‖a‖*‖b‖*r^2=(3*C0^3*C1^2+6*CP^2)*‖a‖*‖b‖*r^2))
  exact hFull'

theorem actual_first_error_self_commutator (A : NativeTaylorGeneratorBounds s h hK C)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (hCQ : 0 ≤ CQ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {CC CH : ℝ} (hCC : 0 ≤ CC) (a b : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Cb : (j : I) → RelativeCenterErrorCoefficientFamily d y b j CC CH)
    (Ha Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Ha=
      (s.firstAdjointErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hHb : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hb=
      (s.firstAdjointErrorFamily Cb ((y,frameVectorLinear d.frame y),0)).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    let CB := taylorGeneratorFixedBudget F0 ha0 C
    let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
    let CP := 1+CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1+radialScalarEndpointBudget CQ*C1
    GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0))
      (s.firstAdjointHalfErrorFamily Cb ((y,frameVectorLinear d.frame y),0)) Ha Hb
      ((3*C0^3*C1^2+6*CP^2)*‖a‖*‖b‖*(d.radius y)^2) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let r := d.radius y
  let CB := taylorGeneratorFixedBudget F0 ha0 C
  let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  let CZ := radialScalarEndpointBudget CQ
  let CP := 1+CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1+CZ*C1
  let coeff (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := actualFirstErrorGeneratorCoefficients Q0 Cu
  let low (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
    ∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (coeff u Cu k))
  let high (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
    ∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp (closedThreeJetHigherScalarMultiplierL (coeff u Cu k))
  let normal (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) :=
    ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cu j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let zm (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := radialScalarBoundedHalfL ell (normal u Cu)
  let zn (u : X) (Cu : (j : I) → RelativeCenterErrorCoefficientFamily d y u j CC CH) := radialScalarBoundedNegativeL ell (normal u Cu)
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hFull' := A.actual_first_error_self_model_bound hd hK1 hf hε hε1 hy hr1 hCQ hF0 ha0 hFlat hInv0 Q0 hQ0 hCC a b Ca Cb
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  obtain ⟨hLa,hHA⟩ := s.first_error_scalar_endpoint_realization A Ca hF0 Q0 hQ0 hr
  obtain ⟨hLb,hHB⟩ := s.first_error_scalar_endpoint_realization A Cb hF0 Q0 hQ0 hr
  exact hFull'.congr_of_restrictions (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
    (sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)) hLa.symm hLb.symm
    (hHA.trans hHa.symm) (hHB.trans hHb.symm)

end NativeTaylorGeneratorBounds
end ShrinkingSpheres
