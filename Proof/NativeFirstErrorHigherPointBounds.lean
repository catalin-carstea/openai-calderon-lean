import Proof.FirstErrorHigherCommonBudget
import Proof.TaylorScalarHighNorm
import Proof.NativeFirstErrorRadialBounds
import Proof.NativeFirstErrorAdjointRemainderHigher
import Proof.NativeAdjointRemainderHalfNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def NativeFirstErrorHigherPointBounds
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q0 : SmoothCoefficientJets 2)
    {a : X} {CC CH : ℝ} (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) (B : ℝ) : Prop :=
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
  let Q := actualFirstErrorGeneratorCoefficients Q0 C
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((C j).closed p)
  ‖∑ k,(Gh k).comp (closedThreeJetHigherScalarMultiplierL (Q k))‖ ≤ B*‖a‖*(d.radius y) ∧
  ‖∑ k,(Gh k).comp (closedThreeJetHigherScalarMultiplierL (signedTaylorScalarCoefficients Q k))‖ ≤ B*‖a‖*(d.radius y) ∧
  ‖G.firstErrorAdjointRemainderHalfL ha0 Q0 C KN‖ ≤ B*‖a‖*(d.radius y) ∧
  ‖A.firstErrorAdjointRemainderHigher ha0 Q0 C KH‖ ≤ B*‖a‖*(d.radius y) ∧
  ‖radialScalarBoundedHalfL ell N‖ ≤ B*‖a‖*(d.radius y) ∧
  ‖radialScalarBoundedHigherL ell N‖ ≤ B*‖a‖*(d.radius y)

lemma firstErrorHigherPointBounds
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (HS : NativeScalarGeneratorRotationData A ha0 BS) (hBS : 0 ≤ BS)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (hCQ : 0 ≤ CQ)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (CKN : ℝ) (hCKN : 0 ≤ CKN)
    (hKN : ‖KN‖ ≤ CKN*(d.radius y)^2)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) (CKH : ℝ) (hCKH : 0 ≤ CKH)
    (hKH : ‖KH‖ ≤ CKH*(d.radius y)^2)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hR : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient C k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖a‖*(d.radius y)^2) :
    NativeFirstErrorHigherPointBounds A G ha0 Q0 C KN KH
      (firstErrorHigherCommonBudget F0 ha0 Q0 CG CKN CKH BS CQ CI CW K (M 0) CC CR) := by
  let B := firstErrorHigherCommonBudget F0 ha0 Q0 CG CKN CKH BS CQ CI CW K (M 0) CC CR
  let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CKN CQ CI CW K (M 0) CC
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  obtain ⟨_hB1,hCPB,hGB,hRHB,hZHB⟩ := firstErrorHigherCommonBudget_bounds F0 ha0 Q0 CG CKN CKH BS CQ CI CW K (M 0) CC CR
  obtain ⟨_hCP1,_hLowB,hRPB,_hRNB,hZPB⟩ := firstErrorAdjointCommonBudget_bounds F0 ha0 Q0 CG CKN CQ CI CW K (M 0) CC
  have widen (z v : ℝ) (hz : z ≤ v*‖a‖*(d.radius y)) (hv : v ≤ B) : z ≤ B*‖a‖*(d.radius y) :=
    hz.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hv (norm_nonneg _)) hr)
  have hAlpha : 0 ≤ (CB+2)*‖closedThreeJetHigherScalarMultiplierL‖ := by
    have hCB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
    dsimp only [CB]
    positivity
  have hHigh (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
      (hQ : (∑ k,taylorGeneratorWeight (d.radius y) k*‖Q k‖) ≤ C1*‖a‖*(d.radius y)) :
      ‖∑ k,(taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num)
        ((y,frameVectorLinear d.frame y),0)) k).comp (closedThreeJetHigherScalarMultiplierL (Q k))‖ ≤ B*‖a‖*(d.radius y) := by
    have hn := G.scalar_high_combination_norm ha0 Q
    have hh : ‖∑ k,(taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num)
        ((y,frameVectorLinear d.frame y),0)) k).comp (closedThreeJetHigherScalarMultiplierL (Q k))‖ ≤
        ((CB+2)*‖closedThreeJetHigherScalarMultiplierL‖*C1)*‖a‖*(d.radius y) :=
      hn.trans ((mul_le_mul_of_nonneg_left hQ hAlpha).trans_eq (by ring))
    exact widen _ _ hh hGB
  have hQ := hd.first_error_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC a C
  have hSigned : (∑ k,taylorGeneratorWeight (d.radius y) k*
      ‖signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 C) k‖) ≤ C1*‖a‖*(d.radius y) := by
    rw [signedTaylorScalarCoefficients_weighted_sum]
    exact hQ
  have hRP := G.norm_first_error_adjoint_remainder_half hd hK1 hf hε hε1 hy hr1 ha0 hCQ KN CKN hCKN hKN Q0 hCC a C
  have hRH := A.firstErrorAdjointRemainderHigher_norm_le ha0 HS hBS hd hK1 hf hε hε1 hy hr1 hCQ
    KH CKH hCKH hKH Q0 hCC a C CR hCR hR
  have hZP := (s.first_error_radial_endpoint_linear_bounds hd hK1 hf hε hε1 hy hr1 hCQ Q0 hCC a C).1
  have hZH := (s.first_error_radial_higher_bounds hd hK1 hf hε hε1 hy hr1 hCQ Q0 hCC a C).1
  exact ⟨hHigh _ hQ,hHigh _ hSigned,widen _ _ hRP (hRPB.trans hCPB),widen _ _ hRH hRHB,
    widen _ _ hZP (hZPB.trans hCPB),widen _ _ hZH hZHB⟩
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
