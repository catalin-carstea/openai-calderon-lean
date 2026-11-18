import Proof.WeakConormalComparison
import Proof.NativeWeakEnergyData
import Proof.UniformNormalCoefficientCloseness
import Proof.NormalCenterCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma flatCoefficientBound (c : ℝ) : MemLp
    (fun _ : X => TauCeti.PDE.energyIntegrand (c • (1:Mat)) 0 0)
    ⊤ ((volume:Measure X).restrict ballOpens) := memLp_top_const _

/-- The genuine normal coefficients have a common small weak conormal endpoint.
    The scalar is their actual conformal center coefficient, with uniform bounds;
    the native inverse and energy bounds are derived from the frozen geometry. -/
theorem uniform_actual_weak_conormal_comparison {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CC : ℝ,0 < η ∧ 0 ≤ CC ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
      let KP := 4*K^2
      let C := 5*metricDensityBudget KP*KP
      let D := metricDensityBudget KP*KP
      ∃ c : ℝ,c ∈ Icc ((metricDensityBudget KP)⁻¹*KP⁻¹) D ∧ 0 < c ∧
        principalCoefficient H 0 = c • (1:Mat) ∧
      ∃ e : NativeWeakEnergyData (principalCoefficient H) C D,
        ‖nativeWeakConormalEndpoint (principalCoefficient H) (fun _ => (0:X)) (fun _ => (0:ℝ)) e.coefficient_bound sphereFischerInner-
          nativeWeakConormalEndpoint (fun _ : X => c • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ))
            (flatCoefficientBound c) sphereFischerInner‖ ≤ CC*d.radius y := by
  let KP := 4*K^2
  let C := 5*metricDensityBudget KP*KP
  let D := metricDensityBudget KP*KP
  let N := normalPrincipalClosenessBudget hm K M 2
  let CC := sphereSurfaceMass⁻¹*((D*C+1)*9*N*‖fixedHarmonicH1LiftL‖^2)
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith only [hK,sq_nonneg (K-1)]
  have hKPpos : 0 < KP := zero_lt_one.trans_le hKP
  have hC : 0 ≤ C := by dsimp [C,metricDensityBudget];positivity
  have hD : 0 ≤ D := by dsimp [D,metricDensityBudget];positivity
  have hN : 0 ≤ N := by
    dsimp [N,normalPrincipalClosenessBudget,normalMetricClosenessBudget,normalVariationErrorBudget,
      backgroundConnectionDerivativeBudget,metricDensityBudget]
    positivity
  have hCC : 0 ≤ CC := mul_nonneg (inv_nonneg.mpr sphereSurfaceMass_pos.le) (by positivity)
  obtain ⟨ηD,hηD,hData⟩ := uniform_actual_native_weak_energy_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨η0,hη0,h0⟩ := uniform_framed_normal_coefficient_closeness (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηD (min ηE η0),CC,lt_min hηD (lt_min hηE hη0),hCC,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  have hSD := hSmall.trans (min_le_left _ _)
  have hSE := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hS0 := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  have e : NativeWeakEnergyData (principalCoefficient H) C D := hData floor hf ε hε hSD d hd y hy
  have hEll : Elliptic (Metric.closedBall (0:X) 2) KP H := hE floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  obtain ⟨c,hc,hScalar⟩ := hd.1.normal_center_principal_scalar hd.2.1 hy (d.radius y)
  have hcBounds : c ∈ Icc ((metricDensityBudget KP)⁻¹*KP⁻¹) D :=
    hEll.scalar_principal_coefficient_bounds hKP (by simp) c hScalar
  have hDiff (x : X) (hx : x ∈ (ballOpens : Set X)) (i j : I) :
      |principalCoefficient H x i j-(c • (1:Mat)) i j| ≤ N*d.radius y := by
    have hcEntry := congrArg (fun A : Mat => A i j) hScalar
    rw [← hcEntry]
    exact h0 floor hf ε hε hS0 d hd y hy d.g₁ (by simp) x (unitBall_subset_closedBall_two hx) i j
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hb := norm_nativeWeakConormal_sub_flat_le (a:=principalCoefficient H) c e.coefficient_bound
    (flatCoefficientBound c) C D (N*d.radius y) hC hD (mul_nonneg hN hr.le)
    e.inverse_bound e.energy_bound hDiff
  exact ⟨c,hcBounds,hc,hScalar,e,hb.trans_eq (by dsimp only [CC];ring)⟩

end ShrinkingSpheres
