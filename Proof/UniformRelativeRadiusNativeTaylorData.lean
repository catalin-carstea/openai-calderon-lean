import Proof.UniformRelativeRadiusGenerators
import Proof.CommonSupportAffineNativeDerivative
import Proof.CommonSupportTaylorDerivativeData
import Proof.JointMetricCoefficientRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  fullCoefficientOperatorL strongCoefficientOperatorL

/-- Every admitted profile supplies the actual relative-radius family,
    its SAME linear first model and quadratic residual, with all native
    parameter derivative budgets. The relative-radius derivative preserves r². -/
theorem uniform_relative_radius_native_taylor_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C1 CQ : ℝ,0 < η ∧ 0 ≤ C1 ∧ 0 ≤ CQ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A A1 D : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,∃ hD : ContDiff ℝ ∞ D,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (t,z)]
        relativeDilationFamily (normalizedFirstNormalCoefficient d y)) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (t,z)]
        relativeDilationFamily (scalarFirstCoefficient (firstDensityLogCovector d y))) ∧
      (∀ p,D p = A p-d.radius y • A1 p) ∧
      CommonSupportNativeDerivativeBounds A1 hA1 S hS hz1 C1 ∧
      CommonSupportNativeDerivativeBounds D hD S hS hzD (CQ*(d.radius y)^2) ∧
      CommonSupportNativeDerivativeBounds A hA S hS hz ((C1+CQ)*d.radius y) ∧
      ∀ F0 : SmoothCoefficientMatrix 2,
        CommonSupportTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 (d.radius y) F0 (CQ*(d.radius y)^2) := by
  obtain ⟨η,C1,CQ,hη,hC1,hCQ,hData⟩ := uniform_relative_radius_coefficient_generators hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min η 1,C1,CQ,lt_min hη zero_lt_one,hC1,hCQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hRep,hRep1,hField,
    b1,hb1,hzb1,hCurve1,hV1,hD1,bD,hbD,hzbD,hCurveD,hVD,hDD,hScalar⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  have hN1 := commonSupport_native_derivatives_of_generator_bounds A1 hA1 S hS hz1 b1 hb1 hzb1 hCurve1 C1 hC1 hV1 hD1
  have hND := commonSupport_native_derivatives_of_generator_bounds D hD S hS hzD bD hbD hzbD hCurveD (CQ*r^2) (by positivity) hVD hDD
  have hNA := commonSupport_affine_native_derivative_bounds A A1 D hA hA1 hD S S S hS hS hS hz hz1 hzD
    r C1 CQ hr.le hr1 hC1 hCQ hField hN1 hND
  refine ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hRep,hRep1,hField,hN1,hND,hNA,?_⟩
  intro F0
  exact commonSupport_taylor_derivative_bounds_of_residual A A1 D hA hA1 hD S S S hS hS hS hz hz1 hzD
    r (CQ*r^2) F0 hField hND V hV h0V (fun t z => ((1+t) • firstDensityLogCovector d y) z) hScalar

end ShrinkingSpheres
