import Proof.NativeWeakTaylorData
import Proof.NormalizedNativeWeakEnergyData
import Proof.NormalizedStrongTaylorPointData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Every same actual normalized coefficient and canonical first-model point
    representative has uniform native weak inverse and Poisson Taylor bounds. -/
theorem uniform_normalized_weak_taylor_point_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η P Q CP1 CP2 : ℝ,0 < η ∧ 0 ≤ P ∧ 0 ≤ Q ∧ 0 ≤ CP1 ∧ 0 ≤ CP2 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ F F1 : SmoothCoefficientMatrix 2,
      (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 z]
        (fun w => normalizedFirstNormalCoefficient d y w i j)) →
      (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 z]
        (fun w => firstDensityLogCovector d y w*(1:Mat) i j)) →
      NativeWeakTaylorData (coefficientMatrixField 2 F) (coefficientMatrixField 2 F1) 1 (d.radius y)
        (5*K*metricDensityBudget (4*K^2)*(4*K^2)) (K*metricDensityBudget (4*K^2)*(4*K^2)) P Q CP1 CP2 ∧
      RawAffineCoefficientBounds (coefficientMatrixField 2 F) (coefficientMatrixField 2 F1) 1 (d.radius y) P Q := by
  obtain ⟨ηS,CI,P,Q,F0,hηS,hCI,hP,hQ,hF0,hStrong⟩ :=
    uniform_normalized_strong_taylor_point_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,hηW,hWeak⟩ := uniform_normalized_native_weak_energy_data (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  let CW := 5*K*metricDensityBudget (4*K^2)*(4*K^2)
  let DA := K*metricDensityBudget (4*K^2)*(4*K^2)
  let CP1 := 5*(9*P)*‖fixedHarmonicH1LiftL‖
  let CP2 := CW*(9*Q+5*(9*(P+Q))*(9*P))*‖fixedHarmonicH1LiftL‖
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCW : 0 ≤ CW := by dsimp [CW,metricDensityBudget];positivity
  have hN : 0 ≤ ‖fixedHarmonicH1LiftL‖ := norm_nonneg _
  have hCP1 : 0 ≤ CP1 := by
    change 0 ≤ 5*(9*P)*‖fixedHarmonicH1LiftL‖
    positivity
  have hCP2 : 0 ≤ CP2 := by
    change 0 ≤ CW*(9*Q+5*(9*(P+Q))*(9*P))*‖fixedHarmonicH1LiftL‖
    positivity
  refine ⟨min ηS (min ηW 1),P,Q,CP1,CP2,lt_min hηS (lt_min hηW zero_lt_one),hP,hQ,hCP1,hCP2,?_⟩
  intro floor hf ε hε hSmall d hd y hy F F1 hRep hRep1
  obtain ⟨hInv,hInvNorm,hInv0,hInv0Norm,hVal1,hDer1,hValR,hDerR⟩ :=
    hStrong floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy F F1 hRep hRep1
  let a := coefficientMatrixField 2 F
  let a1 := coefficientMatrixField 2 F1
  let r := d.radius y
  have hAeq (z : X) (hz : z ∈ (ballOpens:Set X)) : a z = normalizedFirstNormalCoefficient d y z := by
    ext i j;exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  have e : NativeWeakEnergyData a CW DA := hWeak floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy a
    (aestronglyMeasurable_coefficientMatrixField 2 F) hAeq
  have ha1 := memLp_coefficient_energy_of_entry_bound F1 P hP hVal1
  have hA1 (z : X) (hz : z ∈ (ballOpens:Set X)) (i j : I) : |a1 z i j| ≤ P := hVal1 i j z hz
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hFlatInv : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)‖ ≤ 5 := by
    change ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat))
      (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) (flatCoefficientBound 1)‖ ≤ 5
    simpa only [inv_one,mul_one] using (flat_native_weak_energy_data 1 (by norm_num)).inverse_bound
  have hR (z : X) (hz : z ∈ (ballOpens:Set X)) (i j : I) : |(a z-(1:ℝ) • (1:Mat)-r • a1 z) i j| ≤ Q*r^2 := by
    have hFlat := congrArg (fun A : Mat => A i j) (hF0 z (unitBall_subset_closedBall_two hz))
    change coefficientValue 2 (F0 i j) z = (1:Mat) i j at hFlat
    have hEq : coefficientValue 2 ((F-F0-r • F1) i j) z = (a z-(1:ℝ) • (1:Mat)-r • a1 z) i j := by
      simp only [Pi.sub_apply,Pi.smul_apply,coefficientValue_sub_local,coefficientValue_smul,
        Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,one_mul]
      change coefficientValue 2 (F i j) z-coefficientValue 2 (F0 i j) z-r*coefficientValue 2 (F1 i j) z = _
      rw [hFlat]
      rfl
    rw [← hEq]
    exact hValR i j z hz
  exact nativeWeakTaylorData_with_entries_of_affine_bounds 1 r CW DA 5 P Q (by norm_num) hr.le hr1 hCW (by norm_num) hP hQ
    e ha1 hFlatInv hA1 hR

end ShrinkingSpheres
