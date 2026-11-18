import Proof.NativeScalarBoundedHigherData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Enlarge scalar, bounded and angular budgets without changing any
actual coefficient or genuine higher endpoint witness. -/
def NativeScalarBoundedHigherData.enlarge
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {T : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB CAug scale CQB' CZB' CAug' : ℝ}
    {L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}
    {B : NativeScalarBoundedEndpointData T L H CQB CZB scale}
    (D : NativeScalarBoundedHigherData B CAug)
    (hScale : 0 ≤ scale) (hQ : CQB ≤ CQB') (hZ : CZB ≤ CZB') (hAug : CAug ≤ CAug') :
    NativeScalarBoundedHigherData (B.enlarge hScale hQ hZ) CAug' := {
  angular := D.angular
  angular_half := D.angular_half
  augmented_bound := D.augmented_bound.trans (mul_le_mul_of_nonneg_right hAug hScale)
  boundedHigher := D.boundedHigher
  boundedAdjointHigher := D.boundedAdjointHigher
  boundedHigher_pair := D.boundedHigher_pair
  boundedAdjointHigher_pair := D.boundedAdjointHigher_pair
  higher_bounds := ⟨D.higher_bounds.1.trans (mul_le_mul_of_nonneg_right hZ hScale),
    D.higher_bounds.2.trans (mul_le_mul_of_nonneg_right hZ hScale)⟩ }
end ShrinkingSpheres
