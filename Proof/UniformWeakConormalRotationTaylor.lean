import Proof.RotatedWeakConormalDerivative
import Proof.UniformFirstCoefficientTaylor
import Proof.EnlargedFramedEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse nativeWeakHalfLift weakFirstPoissonVariationL

/-- The actual whole-angle weak conormal Taylor remainder has a uniform
    quadratic angle derivative for every admitted radius and smooth frame. -/
theorem uniform_actual_weak_conormal_rotation_taylor {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CN : ℝ,0 < η ∧ 0 ≤ CN ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
        ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      ∃ a1 : ℝ × X → Mat,∃ ha1 : ContDiff ℝ ∞ a1,∃ S1 : Set X,∃ hS1 : IsCompact S1,
        ∃ hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0,
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) v.2) ((θ,0),z)) ∧
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a1 (θ,z) = ell (coordinateRotation i j θ z) • (1:Mat)) ∧
        ‖fderiv ℝ (fun θ => commonSupportWeakConormalEndpoint a ha θ-c • fixedLowRadialL-
          r • weakFirstConormalVariationL c (fun z => a1 (θ,z)) (commonSupportEnergyMemLp a1 ha1 θ)) 0‖ ≤ CN*r^2 := by
  have hOperatorTheorem := uniform_actual_rotated_weak_operator_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηO,CT,hηO,hCT,hOperator⟩ := hOperatorTheorem
  have hTaylorTheorem := uniform_first_coefficient_taylor (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηT,Q,hηT,hQ,hTaylor⟩ := hTaylorTheorem
  have hEllTheorem := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηE,hηE,hEll⟩ := hEllTheorem
  let KP := 4*K^2
  let C0 := 5*K
  let PG := K^3*|M ⟨1,by omega⟩|
  let CN := weakRotationConormalDerivativeBudget KP C0 CT PG Q
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith [sq_nonneg (K-1)]
  have hC0 : 0 ≤ C0 := by dsimp [C0];positivity
  have hPG : 0 ≤ PG := by dsimp [PG];positivity
  have hCN : 0 ≤ CN := weakRotationConormalDerivativeBudget_nonneg KP C0 CT PG Q hKP hC0 hCT hPG hQ
  refine ⟨min ηO (min ηT (min ηE 1)),CN,lt_min hηO (lt_min hηT (lt_min hηE zero_lt_one)),hCN,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  dsimp only
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  let H := framedNormalMetric d.g₁ d.frame d.expMap y r
  have hSO := hSmall.trans (min_le_left _ _)
  have hST := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSE := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hData := hOperator floor hf ε hε hSO d hd y hy i j
  obtain ⟨a,ha,S,hS,hz,a1,ha1,S1,hS1,hz1,hRep,hRep1,hDA,hDE,hDT1,hDQW,hDQF⟩ := hData
  have hEH : Elliptic (Metric.closedBall (0:X) 2) KP H := hEll floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hCenter := hd.2.1.center_mem hy
  have hLn : ‖ell‖ ≤ PG := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
    have hEn := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
    have hD := (hd.1.firstMetricDensityFactor_jet_bounds hΩ hKpos (by omega) hCenter).1
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hD hEn (norm_nonneg _) (by positivity)).trans_eq (by dsimp [PG];ring))
  have hA0 (z : X) (hzB : z ∈ (ballOpens:Set X)) : a (0,z) = principalCoefficient H z := by
    simpa only [coordinateRotationPrincipalFamily_zero_angle] using hRep 0 z (unitBall_subset_closedBall_two hzB)
  have hA10 (z : X) (hzB : z ∈ (ballOpens:Set X)) : a1 (0,z) = ell z • (1:Mat) := by
    simpa only [coordinateRotation_zero] using hRep1 0 z (unitBall_subset_closedBall_two hzB)
  have hFirst (z : X) (hzB : z ∈ (ballOpens:Set X)) (k l : I) : |a1 (0,z) k l| ≤ PG := by
    rw [hA10 z hzB]
    have hBall : z ∈ Metric.ball (0:X) 1 := hzB
    have hzNorm : ‖z‖ ≤ 1 := le_of_lt (by
      simpa only [Metric.mem_ball,dist_zero_right] using hBall)
    have hValue : |ell z| ≤ PG := (ell.le_opNorm z).trans ((mul_le_mul hLn hzNorm (norm_nonneg z) hPG).trans_eq (by ring))
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs
    · simpa only [mul_one] using hValue
    · simpa only [mul_zero,abs_zero] using hPG
  have hTaylorPoint (z : X) (hzB : z ∈ (ballOpens:Set X)) (k l : I) :
      |(a (0,z)-c • (1:Mat)-r • a1 (0,z)) k l| ≤ Q*r^2 := by
    have ht := (hTaylor floor hf ε hε hST d hd y hy z (unitBall_subset_closedBall_two hzB) k l).1
    rw [hA0 z hzB,hA10 z hzB]
    convert ht using 1 <;> simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] <;> congr 1 <;> ring
  have hcinv : c⁻¹ ≤ K := hd.1.firstMetricDensityFactor_inverse_le hKpos hCenter
  have hFlat := flat_native_weak_energy_data c hc
  have hI0 : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0 :=
    hFlat.inverse_bound.trans (mul_le_mul_of_nonneg_left hcinv (by norm_num))
  refine ⟨a,ha,S,hS,hz,a1,ha1,S1,hS1,hz1,hRep,hRep1,?_⟩
  exact norm_rotated_commonSupportWeakConormal_taylor_derivative_le H KP hKP hEH i j
    a a1 ha ha1 S S1 hS hS1 hz hz1 c r C0 CT PG Q hc hr.le hr1 hC0 hCT hPG hQ
    (fun θ z hzB => hRep θ z (unitBall_subset_closedBall_two hzB)) hFirst hTaylorPoint hI0
    hDA hDE hDT1 hDQW hDQF

end ShrinkingSpheres
