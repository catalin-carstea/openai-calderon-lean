import Proof.CommonSupportTaylorDerivativeData
import Proof.UniformParallelOperatorTaylorData

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
open OAI.AnisotropicCalderon.SphereHarmonic

/-- One actual parallel-center coefficient family supplies every native
    principal/first/residual and Taylor derivative input, including quadratic
    tangential cancellation. Baseline cutoff choices do not affect derivatives. -/
theorem uniform_parallel_native_taylor_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C1 CQ : ℝ,0 < η ∧ 0 ≤ C1 ∧ 0 ≤ CQ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
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
      CommonSupportNativeDerivativeBounds A1 hA1 S hS hz1 (C1*‖a‖) ∧
      CommonSupportNativeDerivativeBounds D hD S hS hzD (CQ*(d.radius y)^2*‖a‖) ∧
      CommonSupportNativeDerivativeBounds A hA S hS hz ((C1+CQ)*d.radius y*‖a‖) ∧
      ∀ F0 : SmoothCoefficientMatrix 2,
        CommonSupportTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 (d.radius y) F0 (CQ*(d.radius y)^2*‖a‖) := by
  obtain ⟨η,C1,CQ,hη,hC1,hCQ,hData⟩ := uniform_parallel_operator_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C1,CQ,hη,hC1,hCQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hDField,hN1,hND,hNA⟩ :=
    hData floor hf ε hε hSmall d hd y hy a
  refine ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hDField,hN1,hND,hNA,?_⟩
  intro F0
  apply commonSupport_taylor_derivative_bounds_of_residual A A1 D hA hA1 hD S S S hS hS hS hz hz1 hzD
    (d.radius y) (CQ*(d.radius y)^2*‖a‖) F0 hDField hND V hV h0V
    (fun t z => parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) t z)
  intro t ht w
  have hw : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num)
    (Metric.sphere_subset_closedBall w.property)
  exact (hRep1 t ht w.val hw).eq_of_nhds

end ShrinkingSpheres
