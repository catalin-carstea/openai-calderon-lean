import Proof.HalfMultiplierTaylorBudget
import Proof.NormalizedWeakTaylorPointData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse nativeCoefficientWeakFunctionalInverse

/-- Uniform quadratic gained multiplier commutators for EVERY admitted
profile and every actual normalized coefficient representative. The multiplier
is charged only its physical-ball two-jet bound. No frame derivatives enter. -/
theorem uniform_normalized_multiplier_commutator_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CGain : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
    ∃ ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens),
    0 < η ∧ 0 ≤ CGain ∧
    (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
    ∀ F F1 : SmoothCoefficientMatrix 2,
    (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 z]
      (fun w => normalizedFirstNormalCoefficient d y w i j)) →
    (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 z]
      (fun w => firstDensityLogCovector d y w*(1:Mat) i j)) →
    ∃ ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens),
    ∃ ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens),
    IsCoercive (TauCeti.PDE.energyFormH1L0 ha) ∧
    (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
    (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible ∧
    ∀ Qm : SmoothCoefficientJets 3,∀ B : ℝ,0 ≤ B →
    (∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Qm) z) j| ≤ B) →
    (∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Qm) w) j) z‖ ≤ B) →
    ‖halfRadialMultiplierCommutatorL F ha Qm-halfRadialMultiplierCommutatorL F0 ha0 Qm-
      d.radius y • halfMultiplierFirstVariationL F0 F1 ha1 Qm‖ ≤ CGain*B*(d.radius y)^2 := by
  obtain ⟨ηS,C,P,Q,F0,hηS,hC,hP,hQ,hFlat,hStrong⟩ :=
    uniform_normalized_strong_taylor_point_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,Pw,Qw,CP1,CP2,hηW,hPw,hQw,hCP1,hCP2,hWeak⟩ :=
    uniform_normalized_weak_taylor_point_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  have hFlatB (z : X) (hz : z ∈ (ballOpens:Set X)) := hFlat z (unitBall_subset_closedBall_two hz)
  have hF0Jets := flat_compact_coefficient_local_jets F0 hFlatB
  have ha0 := memLp_coefficient_energy_of_entry_bound F0 1 (by norm_num) hF0Jets.1
  let q := 1+P+Q
  let CGain := halfMultiplierTaylorUniformBudget C P Q q CP1 CP2
  have hq : 0 ≤ q := by dsimp [q];positivity
  have hCGain : 0 ≤ CGain := halfMultiplierTaylorUniformBudget_nonneg C P Q q CP1 CP2 hC hP hQ hq hCP1 hCP2
  refine ⟨min ηS (min ηW 1),CGain,F0,ha0,lt_min hηS (lt_min hηW zero_lt_one),hCGain,hFlat,?_⟩
  intro floor hf ε hε hSmall d hd y hy F F1 hRep hRep1
  obtain ⟨hInv,hNI,hInv0,hNI0,hVal1,hDer1,hValR,hDerR⟩ :=
    hStrong floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy F F1 hRep hRep1
  obtain ⟨t,hRaw⟩ := hWeak floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy F F1 hRep hRep1
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hValF,hDerF⟩ := coefficient_local_C1_of_flat_affine F F0 F1 (d.radius y) P Q
    hr.le hr1 hP hQ hFlatB hVal1 hDer1 hValR hDerR
  refine ⟨t.energy.coefficient_bound,t.first_coefficient_bound,t.energy.coercive,hInv,hInv0,?_⟩
  intro Qm B hB hQ1 hQ2
  have hCore := norm_halfMultiplierCommutator_first_remainder_local_C1 F F0 F1 Qm
    (d.radius y) C _ _ Pw Qw CP1 CP2 P Q q B hr.le hr1 hC hP hQ hq hB hCP1 hCP2 t ha0
    hFlatB hInv hInv0 hNI hNI0 hVal1 hDer1 hValR hDerR hValF hDerF hQ1 hQ2
  have hBudget := halfMultiplierTaylorPointBudget_le_uniform F0 Qm C P Q q B CP1 CP2
    hC hP hQ hq hB hCP1 hCP2 hFlatB hQ1 hQ2
  exact hCore.trans (mul_le_mul_of_nonneg_right hBudget (sq_nonneg _))

end ShrinkingSpheres
