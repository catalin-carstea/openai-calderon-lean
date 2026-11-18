import Proof.UniformParallelResidualGenerators
import Proof.ParallelFirstModelGenerator
import Proof.AffineCoefficientGenerator
import Proof.CommonSupportOneBoundaryTaylorDerivative

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

/-- One genuine actual parallel-center family supplies the principal,
    canonical first-model and quadratic native derivative budgets together. -/
theorem uniform_parallel_one_boundary_taylor_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
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
      CommonSupportOneBoundaryDerivativeBounds A1 hA1 S hS hz1 (C1*‖a‖) ∧
      CommonSupportOneBoundaryDerivativeBounds D hD S hS hzD (CQ*(d.radius y)^2*‖a‖) ∧
      CommonSupportOneBoundaryDerivativeBounds A hA S hS hz ((C1+CQ)*d.radius y*‖a‖) ∧
      CommonSupportOneBoundaryTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 (d.radius y) (CQ*(d.radius y)^2*‖a‖) := by
  obtain ⟨η,CQ,hη,hCQ,hData⟩ := uniform_parallel_coefficient_residual_generators hY hΩ hm K ρ c₀ M Cj hK hρ
  let C1 := parallelFirstModelDerivativeBudget (by omega : 2 ≤ m) K M
  have hC1 : 0 ≤ C1 := by dsimp [C1,parallelFirstModelDerivativeBudget];positivity
  refine ⟨min η 1,C1,CQ,lt_min hη zero_lt_one,hC1,hCQ,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hField,bD,hbD,hzbD,hCurveD,hVD,hDD⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy a
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  obtain ⟨b1,hb1,hzb1,hCurve1,hV1,hD1⟩ := hd.1.parallel_first_model_generator_bounds hΩ hK (by omega)
    (hd.2.1.center_mem hy) a A1 hA1 S hS hz1 (fun z hzB => hRep1 0 h0V z hzB)
  have hB1 : CommonSupportOneBoundaryDerivativeBounds A1 hA1 S hS hz1 (C1*‖a‖) :=
    commonSupport_one_boundary_derivatives_of_generator_bounds A1 hA1 S hS hz1 b1 hb1 hzb1 hCurve1
      (C1*‖a‖) (by positivity) hV1 hD1
  have hBD : CommonSupportOneBoundaryDerivativeBounds D hD S hS hzD (CQ*r^2*‖a‖) :=
    commonSupport_one_boundary_derivatives_of_generator_bounds D hD S hS hzD bD hbD hzbD hCurveD
      (CQ*r^2*‖a‖) (by positivity) hVD hDD
  obtain ⟨bA,hbA,hzbA,hCurveA,hVA,hDA⟩ := commonSupport_affine_generator_bounds A A1 D S r
    (C1*‖a‖) (CQ*‖a‖) hr.le hr1 (by positivity) (by positivity) hField b1 bD hb1 hbD hzb1 hzbD hCurve1 hCurveD
    hV1 hD1 (fun z hzB => (hVD z hzB).trans_eq (by ring)) (fun z hzB => (hDD z hzB).trans_eq (by ring))
  have hBA0 := commonSupport_one_boundary_derivatives_of_generator_bounds A hA S hS hz bA hbA hzbA hCurveA
    ((C1*‖a‖+CQ*‖a‖)*r) (by positivity) hVA hDA
  have hRate : (C1*‖a‖+CQ*‖a‖)*r = (C1+CQ)*r*‖a‖ := by ring
  have hBA : CommonSupportOneBoundaryDerivativeBounds A hA S hS hz ((C1+CQ)*r*‖a‖) := hRate ▸ hBA0
  let s := fun t z => parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y) t z
  have hScalar (t : ℝ) (ht : t ∈ V) (w : OAI.AnisotropicCalderon.SphereHarmonic.UnitSphere) :
      A1 (t,w.val) = s t w.val • (1:Mat) :=
    (hRep1 t ht w.val (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property))).eq_of_nhds
  have hTaylor := commonSupport_one_boundary_taylor_derivatives A A1 D hA hA1 hD S S S hS hS hS hz hz1 hzD
    r (CQ*r^2*‖a‖) hField V hV h0V s hScalar hBD
  exact ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hField,hB1,hBD,hBA,hTaylor⟩

end ShrinkingSpheres
