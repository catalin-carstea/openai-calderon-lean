import Proof.NativeAdjointRemainderHalfNorm
import Proof.TaylorScalarHighNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def firstErrorAdjointHigherNormBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q0 : SmoothCoefficientJets 2) (CG CK CQ K M0 CC : ℝ) : ℝ :=
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M0| *K+3*K+15*CC)
  |(((CB+2)*‖closedThreeJetHigherScalarMultiplierL‖+
    (‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB+radialScalarEndpointBudget CQ))*C1)|

namespace NativeTaylorGeneratorBounds
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- The SAME already constructed higher adjoint endpoint has a linear
    radius norm bound. This uses the public signed scalar-combination and
    remainder estimates; higher norm is not inferred from the low endpoint. -/
lemma norm_firstErrorAdjointHigherL_le (A : NativeTaylorGeneratorBounds s h hK CG)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (hCQ : 0 ≤ CQ)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CK : ℝ) (hCK : 0 ≤ CK) (hKN : ‖KN‖ ≤ CK*(d.radius y)^2)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (Ca : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH) :
    ‖A.firstErrorAdjointHigherL ha0 Q0 Ca KN‖ ≤
      firstErrorAdjointHigherNormBudget F0 ha0 Q0 CG CK CQ K (M 0) CC*‖a‖*d.radius y := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let Q := actualFirstErrorGeneratorCoefficients Q0 Ca
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let C1 := firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC)
  let RH := ‖closedThreeJetHalfBoundaryScalarMultiplierL‖*CK+CB+radialScalarEndpointBudget CQ
  let GH := (CB+2)*‖closedThreeJetHigherScalarMultiplierL‖
  have hr := (hd.2.2.2.2.1.2 y hy).1.le
  have hGH : 0 ≤ GH := by
    have hCB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
    dsimp only [GH,CB]
    positivity
  have hQ := hd.first_error_scalar_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC a Ca
  have hSigned : (∑ k,taylorGeneratorWeight (d.radius y) k*‖signedTaylorScalarCoefficients Q k‖) ≤ C1*‖a‖*d.radius y := by
    rw [signedTaylorScalarCoefficients_weighted_sum]
    exact hQ
  have hHigh : ‖∑ k,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) k).comp
      (closedThreeJetHigherScalarMultiplierL (signedTaylorScalarCoefficients Q k))‖ ≤ (GH*C1)*‖a‖*d.radius y :=
    (A.scalar_high_combination_norm ha0 (signedTaylorScalarCoefficients Q)).trans
      ((mul_le_mul_of_nonneg_left hSigned hGH).trans_eq (by ring))
  have hRem := A.norm_first_error_adjoint_remainder_half hd hK1 hf hε hε1 hy hr1 ha0 hCQ KN CK hCK hKN Q0 hCC a Ca
  have hComp : ‖(A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))‖ ≤ (RH*C1)*‖a‖*d.radius y :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _)
        (norm_nonneg (A.firstErrorAdjointRemainderHalfL ha0 Q0 Ca KN))).trans_eq (mul_one _)).trans hRem)
  have hRaw : ‖A.firstErrorAdjointHigherL ha0 Q0 Ca KN‖ ≤ ((GH+RH)*C1)*‖a‖*d.radius y :=
    (norm_add_le _ _).trans ((add_le_add hHigh hComp).trans_eq (by ring))
  exact hRaw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self ((GH+RH)*C1)) (norm_nonneg a)) hr)
end NativeTaylorGeneratorBounds
end ShrinkingSpheres
