import Proof.UniformParallelResidualGenerators
import Proof.ParallelCoefficientPairFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Subtract the same compact first model. The constant flat coefficient
    disappears from parameter derivatives, so no noncompact residual is introduced. -/
theorem commonSupport_affine_residual_native_bounds
    (A A1 : ℝ × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S : Set X) (hS : IsCompact S) (hz : ∀ t z,z ∉ S → A (t,z) = 0)
    (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0) (r q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),∀ i j,
      |fderiv ℝ (fun p => A p i j-(1:Mat) i j-r*A1 p i j) (0,z) (1,0)| ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),∀ v : X,∀ i j,
      |fderiv ℝ (fderiv ℝ (fun p => A p i j-(1:Mat) i j-r*A1 p i j)) (0,z) (0,v) (1,0)| ≤ q*‖v‖) :
    ∃ D : ℝ × X → Mat,∃ hD : ContDiff ℝ ∞ D,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      (∀ p,D p = A p-r • A1 p) ∧ CommonSupportNativeDerivativeBounds D hD S hS hzD q := by
  obtain ⟨D,hD,hzD,hField,b,hb,hzb,hCurve,hValue,hSpatial⟩ :=
    commonSupport_affine_residual_generator_bounds A A1 hA hA1 S hS hz hz1 r q hq h0 h1
  exact ⟨D,hD,hzD,hField,commonSupport_native_derivatives_of_generator_bounds
    D hD S hS hzD b hb hzb hCurve q hq hValue hSpatial⟩

/-- For every admitted profile, the actual local parallel-center family has
    uniformly quadratic native derivatives after its SAME first-model subtraction. -/
theorem uniform_parallel_coefficient_residual_native {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∃ A A1 D : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,∃ hD : ContDiff ℝ ∞ D,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧ (∀ t ∈ V,y+t • a ∈ Y) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (t,z)]
        parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a (d.radius y) (frameVectorLinear d.frame y)) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (t,z)]
        parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) ∧
      (∀ p,D p = A p-d.radius y • A1 p) ∧
      CommonSupportNativeDerivativeBounds D hD S hS hzD (C*(d.radius y)^2*‖a‖) := by
  obtain ⟨η,C,hη,hC,hData⟩ := uniform_parallel_coefficient_residual_generators hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hField,b,hb,hzb,hCurve,hValue,hSpatial⟩ :=
    hData floor hf ε hε hSmall d hd y hy a
  have hNative := commonSupport_native_derivatives_of_generator_bounds D hD S hS hzD b hb hzb hCurve
    (C*(d.radius y)^2*‖a‖) (by positivity) hValue hSpatial
  exact ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hField,hNative⟩

end ShrinkingSpheres
