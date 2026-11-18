import Proof.NativeWeakTaylorData
import Proof.WeakFirstVariationNorm
import Proof.FlatNativeWeakData
import Proof.FlatCanonicalWeakInverse
import Proof.UniformFirstStrongTaylorData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Uniform quadratic weak Poisson Taylor data for the actual normal metric,
    with all weak inverse and coefficient witnesses supplied by the admitted geometry. -/
theorem uniform_actual_weak_poisson_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η P Q CP1 CP2 : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ 0 ≤ P ∧ 0 ≤ Q ∧ 0 ≤ CP1 ∧ 0 ≤ CP2 ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let KP := 4*K^2
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let ℓ := firstDensityCenterLinearL d y
      ∃ F F1 : SmoothCoefficientMatrix 2,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => ℓ z*(1:Mat) i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 ((F-c • F0-d.radius y • F1) i j) x| ≤ Q*(d.radius y)^2) ∧
        (∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-d.radius y • F1) i j)) x‖ ≤ Q*(d.radius y)^2) ∧
        NativeWeakTaylorData a (coefficientMatrixField 2 F1) c (d.radius y)
          (5*metricDensityBudget KP*KP) (metricDensityBudget KP*KP) P Q CP1 CP2 := by
  obtain ⟨ηS,CS,P,Q,F0,hηS,hCS,hP,hQ,hF0,hStrong⟩ :=
    uniform_first_strong_taylor_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,hηW,hWeak⟩ := uniform_actual_native_weak_energy_data
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  let KP := 4*K^2
  let CW := 5*metricDensityBudget KP*KP
  let DA := metricDensityBudget KP*KP
  let C0 := 5*K
  let CP1 := C0*(9*P)*‖fixedHarmonicH1LiftL‖
  let CP2 := CW*(9*Q+C0*(9*(P+Q))*(9*P))*‖fixedHarmonicH1LiftL‖
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCW : 0 ≤ CW := by dsimp [CW,metricDensityBudget];positivity
  have hC0 : 0 ≤ C0 := by dsimp [C0];positivity
  have hCP1 : 0 ≤ CP1 := by
    change 0 ≤ C0*(9*P)*‖fixedHarmonicH1LiftL‖
    exact mul_nonneg (mul_nonneg hC0 (mul_nonneg (by norm_num) hP)) (norm_nonneg _)
  have hCP2 : 0 ≤ CP2 := by
    change 0 ≤ CW*(9*Q+C0*(9*(P+Q))*(9*P))*‖fixedHarmonicH1LiftL‖
    exact mul_nonneg (mul_nonneg hCW (add_nonneg (by positivity)
      (mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity)))) (norm_nonneg _)
  refine ⟨min (min ηS ηW) 1,P,Q,CP1,CP2,F0,lt_min (lt_min hηS hηW) zero_lt_one,hP,hQ,hCP1,hCP2,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  obtain ⟨F,F1,hRep,hRep1,hInv,hNorm,hInv0,hNorm0,hVal1,hDeriv1,hValR,hDerivR⟩ :=
    hStrong floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  let a1 := coefficientMatrixField 2 F1
  have e : NativeWeakEnergyData a CW DA :=
    hWeak floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have e0 := flat_native_weak_energy_data c hc
  have hcinv : c⁻¹ ≤ K := hd.1.firstMetricDensityFactor_inverse_le hKpos (hd.2.1.center_mem hy)
  have hFlatInv : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0 :=
    e0.inverse_bound.trans (mul_le_mul_of_nonneg_left hcinv (by norm_num))
  have ha1 := memLp_coefficient_energy_of_entry_bound F1 P hP hVal1
  have hA1 (x : X) (hx : x ∈ (ballOpens:Set X)) (i j : I) : |a1 x i j| ≤ P := hVal1 i j x hx
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  have hR (x : X) (hx : x ∈ (ballOpens:Set X)) (i j : I) : |(a x-c • (1:Mat)-r • a1 x) i j| ≤ Q*r^2 := by
    have hPoint := (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds
    have hFlat := congrArg (fun A : Mat => A i j) (hF0 x (unitBall_subset_closedBall_two hx))
    change coefficientValue 2 (F0 i j) x = (1:Mat) i j at hFlat
    have hEq : coefficientValue 2 ((F-c • F0-r • F1) i j) x = (a x-c • (1:Mat)-r • a1 x) i j := by
      simp only [Pi.sub_apply,Pi.smul_apply,coefficientValue_sub_local,coefficientValue_smul,
        Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
      change coefficientValue 2 (F i j) x-c*coefficientValue 2 (F0 i j) x-r*coefficientValue 2 (F1 i j) x = _
      rw [hPoint,hFlat]
      rfl
    rw [← hEq]
    exact hValR i j x hx
  have hTaylorData := nativeWeakTaylorData_of_affine_bounds c r CW DA C0 P Q hc hr.le hr1 hCW hC0 hP hQ
    e ha1 hFlatInv hA1 hR
  exact ⟨F,F1,hRep,hRep1,hInv,hInv0,hVal1,hDeriv1,hValR,hDerivR,hTaylorData⟩

end ShrinkingSpheres
