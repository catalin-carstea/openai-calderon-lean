import Proof.CommonSupportAffineResidualGenerator
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

/-- For every admitted profile, the actual local parallel-center family has
    uniformly quadratic native derivatives after its SAME first-model subtraction. -/
theorem uniform_parallel_coefficient_residual_generators {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
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
      ∃ b : X → Mat,ContDiff ℝ ∞ b ∧ (∀ z,z ∉ S → b z = 0) ∧
        (∀ z,HasDerivAt (fun t => D (t,z)) (b z) 0) ∧
        (∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ C*(d.radius y)^2*‖a‖) ∧
        ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ C*(d.radius y)^2*‖a‖ := by
  obtain ⟨η,hη,hFamily⟩ := uniform_parallel_coefficient_pair_family hY hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let C0 := uniformParallelFirstCoefficientCenterBudget hm K M 2
  let C1 := uniformParallelFirstCoefficientMixedBudget hm K M 2
  let C := |C0|+|C1|
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  obtain ⟨A,A1,hA,hA1,S,hS,hz,hz1,V,hV,h0V,hVY,hRep,hRep1,hBounds⟩ := hFamily floor hf ε hε hSmall d hd y hy a
  let r := d.radius y
  let q := C*r^2*‖a‖
  have hq : 0 ≤ q := by dsimp [q];positivity
  have h0 (z : X) (hzB : z ∈ (ballOpens:Set X)) (i j : I) :
      |fderiv ℝ (fun p => A p i j-(1:Mat) i j-r*A1 p i j) (0,z) (1,0)| ≤ q := by
    have hb := (hBounds z (unitBall_subset_closedBall_two hzB) (0:X) i j).1
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_abs_self C0).trans (le_add_of_nonneg_right (abs_nonneg C1))) (sq_nonneg r)) (norm_nonneg a))
  have h1 (z : X) (hzB : z ∈ (ballOpens:Set X)) (v : X) (i j : I) :
      |fderiv ℝ (fderiv ℝ (fun p => A p i j-(1:Mat) i j-r*A1 p i j)) (0,z) (0,v) (1,0)| ≤ q*‖v‖ := by
    have hb := (hBounds z (unitBall_subset_closedBall_two hzB) v i j).2
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      ((le_abs_self C1).trans (le_add_of_nonneg_left (abs_nonneg C0))) (sq_nonneg r)) (norm_nonneg a)) (norm_nonneg v))
  obtain ⟨D,hD,hzD,hDField,b,hb,hzb,hCurve,hValue,hSpatial⟩ := commonSupport_affine_residual_generator_bounds A A1 hA hA1 S hS hz hz1 r q hq h0 h1
  exact ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hDField,b,hb,hzb,hCurve,hValue,hSpatial⟩

end ShrinkingSpheres
