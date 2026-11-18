import Proof.RightScalarCombination
import Proof.NativeTaylorGeneratorCoarseEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- One native scalar-generator and bounded-remainder realization of an
actual low/high operator pair. Both endpoints use the SAME scalar family;
no global parameter smoothness is asserted. -/
structure NativeScalarBoundedEndpointData {Y Ω : Set X} {d : Data} {y : X}
    {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (T : NativeTaylorGeneratorBounds s h hK CG)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (CQB CZB scale : ℝ) where
  coefficient : TaylorGeneratorIndex → ClosedCoefficientJets 3
  boundedHalf : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  boundedNegative : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  low_form : L=
    rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)))
      closedThreeJetHalfBoundaryScalarMultiplierL coefficient+
    boundedNegative.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
  high_form : H=
    rightScalarCombinationL (taylorGeneratorHigh
      (T.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)))
      closedThreeJetHigherScalarMultiplierL coefficient+
    boundedHalf.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  bounded_pair : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp boundedHalf=
    boundedNegative.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
  coefficient_bound : (∑ a,taylorGeneratorWeight (d.radius y) a*‖coefficient a‖) ≤ CQB*scale
  bounded_bounds : ‖boundedHalf‖ ≤ CZB*scale ∧ ‖boundedNegative‖ ≤ CZB*scale

def NativeScalarBoundedEndpointData.enlarge
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG}
    {L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    {CQB CZB scale CQB' CZB' : ℝ} (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (hScale : 0 ≤ scale) (hQ : CQB ≤ CQB') (hZ : CZB ≤ CZB') :
    NativeScalarBoundedEndpointData T L H CQB' CZB' scale := {
  coefficient := B.coefficient
  boundedHalf := B.boundedHalf
  boundedNegative := B.boundedNegative
  low_form := B.low_form
  high_form := B.high_form
  bounded_pair := B.bounded_pair
  coefficient_bound := B.coefficient_bound.trans (mul_le_mul_of_nonneg_right hQ hScale)
  bounded_bounds := ⟨B.bounded_bounds.1.trans (mul_le_mul_of_nonneg_right hZ hScale),
    B.bounded_bounds.2.trans (mul_le_mul_of_nonneg_right hZ hScale)⟩ }
end ShrinkingSpheres
