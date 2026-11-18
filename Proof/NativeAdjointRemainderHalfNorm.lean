import Proof.NativeFirstErrorAdjointEndpoints
import Proof.FiniteScalarRemainderNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
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

lemma scalar_adjoint_remainder_half_bound (A : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    ‖taylorScalarAdjointRemainderHalfL KN
      (fun a => taylorGeneratorScalarCommutator A.scalar F0 ha0 a (Q a)) Q‖ ≤
      (‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+taylorGeneratorFixedBudget F0 ha0 CG)*
        (∑ a,taylorGeneratorWeight (d.radius y) a*‖Q a‖) :=
  norm_finite_scalar_remainder_weighted closedThreeJetHalfBoundaryScalarMultiplierL _ _ Q
    (taylorGeneratorWeight (d.radius y)) TaylorGeneratorIndex.adjointSign CK _
    (fun a => by cases a <;> norm_num [TaylorGeneratorIndex.adjointSign])
    (norm_taylorGeneratorAdjointDefectHalfL_le KN CK (d.radius y) hCK hKN)
    (fun a => (A.generator_weight_bounds ha0).2.2 a (Q a))

/-- The positive endpoint of the SAME complete adjoint remainder has the
one-radius bound needed for the higher first-error adjoint endpoint. -/
lemma norm_first_error_adjoint_remainder_half (A : NativeTaylorGeneratorBounds s h hK CG)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (hCQ : 0 ≤ CQ)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH) :
    let CR := ‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+taylorGeneratorFixedBudget F0 ha0 CG
    let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
    ‖A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN‖ ≤
      ((CR+radialScalarEndpointBudget CQ)*C1)*‖a‖*(d.radius y) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  let N := ∑ j : I,closedCoordinateCoefficientProductL Q0 j ((Ca j).closed p)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let CR := ‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+taylorGeneratorFixedBudget F0 ha0 CG
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  let CZ := radialScalarEndpointBudget CQ
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hCB : 0 ≤ taylorGeneratorFixedBudget F0 ha0 CG := zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  have hCR : 0 ≤ CR := add_nonneg (mul_nonneg (norm_nonneg _) hCK) hCB
  have hC1 : 0 ≤ C1 := mul_nonneg (zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1) (by positivity)
  have hEll : ‖ell‖ ≤ CQ := by
    have hh := s.coefficients.firstCovectorJets (by norm_num) 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh
  have hN := hd.normal_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC a Ca
  have hB : 0 ≤ C1*‖a‖*(d.radius y)^2 := mul_nonneg (mul_nonneg hC1 (norm_nonneg _)) (sq_nonneg _)
  have hZ := (norm_radialScalarBounded_endpoints_le CQ hCQ ell hEll N (C1*‖a‖*(d.radius y)^2) hB hN).2
  have hr2 : (d.radius y)^2 ≤ d.radius y := by nlinarith
  have hZr : ‖(radialScalarBoundedNegativeL ell N).adjoint‖ ≤ (CZ*C1)*‖a‖*(d.radius y) := by
    rw [LinearIsometryEquiv.norm_map]
    calc
      _ ≤ CZ*(C1*‖a‖*(d.radius y)^2) := hZ
      _ = (CZ*C1*‖a‖)*(d.radius y)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr2
        (mul_nonneg (mul_nonneg (radialScalarEndpointBudget_pos CQ).le hC1) (norm_nonneg a))
  have hQ := hd.first_error_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC a Ca
  have hR := (A.scalar_adjoint_remainder_half_bound ha0 KN CK hCK hKN Q).trans
    ((mul_le_mul_of_nonneg_left hQ hCR).trans_eq (by ring : CR*(C1*‖a‖*(d.radius y))=(CR*C1)*‖a‖*(d.radius y)))
  exact (norm_add_le _ _).trans ((add_le_add hR hZr).trans_eq (by ring))
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
