import Proof.NativeScalarBoundedEndpointData
import Proof.FullFirstScalarBound
import Proof.FullFirstBoundedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- A single coefficient family realizes the full actual first-base coefficient
at both genuine Sobolev endpoints. The bounded remainders are compatible and
all three bounds use the same scale. No parameter smoothness is asserted here. -/
structure FirstDerivativeScalarData {Y Ω : Set X} {d : Data} {y : X}
    {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (T : NativeTaylorGeneratorBounds s h hK CG) {CDF CDT : ℝ}
    (D : PhysicalPrincipalData Y d CDF CDT) (CQB CZB scale : ℝ) where
  coefficient : I → TaylorGeneratorIndex → ClosedCoefficientJets 3
  boundedHalf : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  boundedNegative : I → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  low_form : ∀ j,D.firstDerivativeHalfL y j=
    rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)))
      closedThreeJetHalfBoundaryScalarMultiplierL (coefficient j)+
    (boundedNegative j).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
  high_form : ∀ j,D.firstDerivativeHigherL y j=
    rightScalarCombinationL (taylorGeneratorHigh
      (T.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)))
      closedThreeJetHigherScalarMultiplierL (coefficient j)+
    (boundedHalf j).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  bounded_pair : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
    (boundedHalf j)=(boundedNegative j).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
  coefficient_bound : ∀ j,(∑ a,taylorGeneratorWeight (d.radius y) a*‖coefficient j a‖) ≤ CQB*scale
  bounded_bounds : ∀ j,‖boundedHalf j‖ ≤ CZB*scale ∧ ‖boundedNegative j‖ ≤ CZB*scale

lemma NativeTaylorGeneratorBounds.full_first_derivative_scalar_data
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (T : NativeTaylorGeneratorBounds s h hK CG)
    {m : ℕ} (hm : 2 ≤ m) {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) (hK1 : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCQ : 0 ≤ CQ) (hy : y ∈ Y)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {CDF CDT CC CH : ℝ} (D : PhysicalPrincipalData Y d CDF CDT) (hCC : 0 ≤ CC)
    (C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH) :
    Nonempty (FirstDerivativeScalarData T D (fullFirstScalarBudget Q0 K (M 0) CC)
      (fullFirstBoundedBudget Q0 CQ K (M 0) (M ⟨1,by omega⟩) CC) (ε/beta d.γ d.radius y)) := by
  have hForm := T.full_first_derivative_scalar_endpoints hd hY hΩ hSub hy hF0 Q0 hQ0 D C
  refine ⟨{
    coefficient := fullFirstScalarCoefficients Q0 C
    boundedHalf := fullFirstBoundedHalfL Q0 C
    boundedNegative := fullFirstBoundedNegativeL Q0 C
    low_form := fun j => (hForm j).1
    high_form := fun j => (hForm j).2
    bounded_pair := full_first_bounded_compatible Q0 C
    coefficient_bound := ?_
    bounded_bounds := ?_ }⟩
  · intro j
    simpa only [mul_div_assoc] using hd.full_first_scalar_weighted_bound hK1 hf hε hε1 Q0 hy hCC C j
  · intro j
    simpa only [mul_div_assoc] using s.norm_full_first_bounded hm hd hΩ hK1 hf hε hε1 hCQ Q0 hy hCC C j
/-- The complete physical first-base coefficient as one canonical native
scalar-plus-bounded packet, shared with leading/full cross commutators. -/
def FirstDerivativeScalarData.endpointData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CDF CDT CQB CZB scale : ℝ}
    {D : PhysicalPrincipalData Y d CDF CDT} (B : FirstDerivativeScalarData T D CQB CZB scale) (j : I) :
    NativeScalarBoundedEndpointData T (D.firstDerivativeHalfL y j) (D.firstDerivativeHigherL y j) CQB CZB scale := {
  coefficient := B.coefficient j
  boundedHalf := B.boundedHalf j
  boundedNegative := B.boundedNegative j
  low_form := B.low_form j
  high_form := B.high_form j
  bounded_pair := B.bounded_pair j
  coefficient_bound := B.coefficient_bound j
  bounded_bounds := B.bounded_bounds j }
end ShrinkingSpheres
