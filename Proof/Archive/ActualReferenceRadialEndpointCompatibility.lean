import Proof.Archive.NativeCoefficientBoundaryMultiplier
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeCoefficientBoundaryMultiplier NativeNegativeHalfSmoothMultiplier
lemma referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (F : SmoothCoefficientJets 2) (m : SmoothData)
    (hDataEq : coefficientSmoothData F = m)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |m.1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient m.1 x‖ ≤ M) :
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 F =
      nativeNegativeHalfSmoothMulL hF hO hD τ0 m hM hm hg := by
  subst m
  exact nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0 F hM hm hg


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
