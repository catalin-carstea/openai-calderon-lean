import Proof.GradedEndpointTwoRestrictionTransport
import Proof.NativeAdjointRemainderHalfNorm
import Proof.FirstErrorAdjointCommonBudget
import Proof.ActualSignedFirstErrorGeneratorCommutator
import Proof.GradedLinearRemainderCommutator
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
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- The complete actual native adjoint first error and unsigned first error
have a quadratically radius-gained, genuine order-one commutator. Both retain
the SAME generators, scalar coefficients, Taylor defect and selected higher
endpoints. The bounded corrections need only ONE radius gain. -/
private theorem actual_first_error_adjoint_model_bound (A : NativeTaylorGeneratorBounds s h hK CG)
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
    {CC CH : ℝ} (hCC : 0 ≤ CC) (a b : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Cb : (j : I) → RelativeCenterErrorCoefficientFamily d y b j CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
 :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let r := d.radius y
    let CB := taylorGeneratorFixedBudget F0 ha0 CG
    let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
    let CZ := radialScalarEndpointBudget CQ
    let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CK CQ CI CW K (M 0) CC
    let Qa := actualFirstErrorGeneratorCoefficients Q0 Ca
    let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
    let low (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
      ∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q k))
    let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
      ∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
    let Nb := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cb j).closed p)
    let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
    let Zp := radialScalarBoundedHalfL ell Nb
    let Zn := radialScalarBoundedNegativeL ell Nb
    let Rp := A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN
    let Rn := nativeFirstErrorAdjointRemainderL s ha0 Q0 Ca KN
    let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    GradedEndpointCommutatorBound I1
      (low (signedTaylorScalarCoefficients Qa)+Rn.comp I0) (low Qb+Zn.comp I0)
      (high (signedTaylorScalarCoefficients Qa)+Rp.comp I1) (high Qb+Zp.comp I1)
      ((3*C0^3*C1^2+6*CP^2)*‖a‖*‖b‖*r^2) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let r := d.radius y
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
  let CZ := radialScalarEndpointBudget CQ
  let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CK CQ CI CW K (M 0) CC
  let Qa := actualFirstErrorGeneratorCoefficients Q0 Ca
  let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
  let low (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
    ∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q k))
  let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
    ∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
  let Nb := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cb j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let Zp := radialScalarBoundedHalfL ell Nb
  let Zn := radialScalarBoundedNegativeL ell Nb
  let Rp := A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN
  let Rn := nativeFirstErrorAdjointRemainderL s ha0 Q0 Ca KN
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  obtain ⟨hCP1,hLC,hRPC,hRNC,hZC⟩ := firstErrorAdjointCommonBudget_bounds F0 ha0 Q0 CG CK CQ CI CW K (M 0) CC
  have hCP : 0 ≤ CP := zero_le_one.trans hCP1
  have hCB : 0 ≤ CB := zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1) (by positivity)
  have hQna := hd.first_error_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC a Ca
  have hQnb := hd.first_error_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC b Cb
  have hQsa : (∑ k,taylorGeneratorWeight r k*‖signedTaylorScalarCoefficients Qa k‖) ≤ C1*‖a‖*r := by
    rw [signedTaylorScalarCoefficients_weighted_sum]
    exact hQna
  have hLow (u : X) (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
      (hQ : (∑ k,taylorGeneratorWeight r k*‖Q k‖) ≤ C1*‖u‖*r) : ‖low Q‖ ≤ CP*‖u‖*r := by
    calc
      _ ≤ (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*(∑ k,taylorGeneratorWeight r k*‖Q k‖) := A.scalar_low_combination_norm ha0 Q
      _ ≤ (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖)*(C1*‖u‖*r) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg hCB (norm_nonneg _))
      _ = (CB*‖closedThreeJetHalfBoundaryScalarMultiplierL‖*C1)*‖u‖*r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLC (norm_nonneg _)) hr.le
  have hRp : ‖Rp‖ ≤ CP*‖a‖*r :=
    (A.norm_first_error_adjoint_remainder_half hd hK1 hf hε hε1 hy hr1 ha0 hCQ KN CK hCK hKN Q0 hCC a Ca).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRPC (norm_nonneg _)) hr.le)
  have hRn : ‖Rn‖ ≤ CP*‖a‖*r :=
    (s.norm_first_error_adjoint_remainder hd hK1 hf hε hε1 hy hr1 hF0 ha0 hCQ hCI hCW KN CK hCK hKN Q0 hCC a Ca).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRNC (norm_nonneg _)) hr.le)
  have hEll : ‖ell‖ ≤ CQ := by
    have hh := s.coefficients.firstCovectorJets (by norm_num) 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh
  have hN := hd.normal_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC b Cb
  have hB : 0 ≤ C1*‖b‖*r^2 := mul_nonneg (mul_nonneg hC1 (norm_nonneg _)) (sq_nonneg _)
  obtain ⟨hZp0,hZn0⟩ := norm_radialScalarBounded_endpoints_le CQ hCQ ell hEll Nb (C1*‖b‖*r^2) hB hN
  have hZ (z : ℝ) (hz : z ≤ CZ*(C1*‖b‖*r^2)) : z ≤ CP*‖b‖*r := by
    have hr2 : r^2 ≤ r := by nlinarith
    calc
      _ ≤ CZ*(C1*‖b‖*r^2) := hz
      _ = (CZ*C1)*‖b‖*r^2 := by ring
      _ ≤ (CZ*C1)*‖b‖*r := mul_le_mul_of_nonneg_left hr2
        (mul_nonneg (mul_nonneg (radialScalarEndpointBudget_pos CQ).le hC1) (norm_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZC (norm_nonneg _)) hr.le
  have hGen := (A.actual_signed_first_error_generator_commutator hd hK1 hf hε hε1 hy hr1 hF0 ha0 hFlat
    s.point.flatStrong Q0 hCC a b Ca Cb).graded_bound
  have hFull := hGen.add_bounded_linear I0 Rp Zp Rn Zn
    (A.scalar_combination_balanced_pair hF0 (signedTaylorScalarCoefficients Qa))
    (A.scalar_combination_balanced_pair hF0 Qb)
    CP ‖a‖ ‖b‖ r hCP (norm_nonneg _) (norm_nonneg _) hr.le
    (norm_sphereSobolevInclusionL_le _ _ _) (hLow a _ hQsa) (hLow b _ hQnb)
    hRp (hZ _ hZp0) hRn (hZ _ hZn0)
  have hFull' := hFull.mono (le_of_eq (by ring :
    (3*C0^3*C1^2)*‖a‖*‖b‖*r^2+6*CP^2*‖a‖*‖b‖*r^2=(3*C0^3*C1^2+6*CP^2)*‖a‖*‖b‖*r^2))
  exact hFull'

theorem actual_first_error_adjoint_commutator (A : NativeTaylorGeneratorBounds s h hK CG)
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
    {CC CH : ℝ} (hCC : 0 ≤ CC) (a b : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Cb : (j : I) → RelativeCenterErrorCoefficientFamily d y b j CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)))
    (Ha Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHa : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hHb : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hb=
      (s.firstAdjointErrorFamily Cb ((y,frameVectorLinear d.frame y),0)).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
    let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
    let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CK CQ CI CW K (M 0) CC
    GradedEndpointCommutatorBound (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (s.firstAdjointHalfErrorFamily Ca p).adjoint (s.firstAdjointHalfErrorFamily Cb p) Ha Hb
      ((3*C0^3*C1^2+6*CP^2)*‖a‖*‖b‖*(d.radius y)^2) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let r := d.radius y
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let C0 := CB+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
  let CZ := radialScalarEndpointBudget CQ
  let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CK CQ CI CW K (M 0) CC
  let Qa := actualFirstErrorGeneratorCoefficients Q0 Ca
  let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
  let low (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
    ∑ k,(taylorGeneratorLow (s.response.adjointHalfTaylor p) k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q k))
  let high (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :=
    ∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp (closedThreeJetHigherScalarMultiplierL (Q k))
  let Nb := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Cb j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let Zp := radialScalarBoundedHalfL ell Nb
  let Zn := radialScalarBoundedNegativeL ell Nb
  let Rp := A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN
  let Rn := nativeFirstErrorAdjointRemainderL s ha0 Q0 Ca KN
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hFull' := A.actual_first_error_adjoint_model_bound hd hK1 hf hε hε1 hy hr1 hCQ hCI hCW hF0 ha0 hFlat Q0 hQ0 hCC a b Ca Cb KN CK hCK hKN hP
  have hLa := A.actual_first_error_adjoint_normal_form Ca hF0 ha0 hFlat Q0 hQ0 hr KN hP
  obtain ⟨hLb,hHB⟩ := s.first_error_scalar_endpoint_realization A Cb hF0 Q0 hQ0 hr
  have hHA := A.first_error_adjoint_balanced_pair hF0 ha0 hFlat Q0 hQ0 Ca hr KN hP
  exact hFull'.congr_of_two_restrictions
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
    (sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num))
    hLa.symm hLb.symm (hHA.trans hHa.symm) (hHB.trans hHb.symm)

end NativeTaylorGeneratorBounds
end ShrinkingSpheres
