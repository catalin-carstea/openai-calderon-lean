import Proof.MetricDensityBounds
import Proof.Archive.TauUniformDirichletInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma Elliptic.contDiffOn_principalCoefficient {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) : ContDiffOn ℝ ∞ (principalCoefficient g) Ω := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact (hg.contDiffOn_density hK).mul (hg.contDiffOn_inverse_entry hK i j)

/-- Explicit uniform ellipticity of the actual divergence-form Laplace coefficient. -/
theorem Elliptic.principalCoefficient_tau {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 1 ≤ K) :
    TauCeti.PDE.UniformlyEllipticOn Ω (principalCoefficient g)
      ((metricDensityBudget K)⁻¹*K⁻¹) (metricDensityBudget K*K) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hB : 0 < metricDensityBudget K := by unfold metricDensityBudget; positivity
  have hB1 : 1 ≤ metricDensityBudget K := by
    have hh : 0 ≤ 6*K^3 := by positivity
    unfold metricDensityBudget
    linarith
  have hBM : (metricDensityBudget K)⁻¹ ≤ metricDensityBudget K := by
    have hh : 1 ≤ metricDensityBudget K*metricDensityBudget K := by nlinarith
    have hMult := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hB.le)
    simpa only [mul_one,← mul_assoc,inv_mul_cancel₀ hB.ne',one_mul] using hMult
  have hw := uniformlyEllipticOn_weightedCoefficient ((hg.inverse_metric hKpos).to_tau_uniformlyEllipticOn hK)
    (inv_pos.mpr hB) hBM (fun x hx => hg.density_bounds hKpos hx)
  change TauCeti.PDE.UniformlyEllipticOn Ω (fun x => metricDensity g x • (g x)⁻¹)
    ((metricDensityBudget K)⁻¹*K⁻¹) (metricDensityBudget K*K)
  exact hw

lemma unitBall_subset_closedBall_two : (ballOpens : Set X) ⊆ Metric.closedBall (0:X) 2 := by
  intro x hx
  have hh : ‖x‖ < 1 := by simpa only [coe_ballOpens,OAI.AnisotropicCalderon.B,Metric.mem_ball,dist_zero_right] using hx
  change dist x 0 ≤ 2
  rw [dist_zero_right]
  linarith

/-- The actual geometric coefficient supplies bounded energy coefficients, coercivity
    and a uniform weak Dirichlet inverse bound on the fixed unit ball. -/
theorem Elliptic.unitBall_dirichlet_data {K : ℝ} {g : MetricField}
    (hg : Elliptic (Metric.closedBall (0:X) 2) K g) (hK : 1 ≤ K) :
    ∃ hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x) 0 0)
        ⊤ ((volume : Measure X).restrict ballOpens),
      IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff) ∧
      ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)‖ ≤ 5*metricDensityBudget K*K := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hSmooth := hg.contDiffOn_principalCoefficient hKpos
  have hUE := (hg.principalCoefficient_tau hK).mono_set unitBall_subset_closedBall_two
  have hMeas : AEStronglyMeasurable (principalCoefficient g) ((volume : Measure X).restrict ballOpens) :=
    (hSmooth.continuousOn.mono unitBall_subset_closedBall_two).aestronglyMeasurable ballOpens.isOpen.measurableSet
  let hcoeff := memLp_zeroDriftEnergyIntegrand hUE hMeas
  refine ⟨hcoeff,isCoercive_unitBall_zeroDrift hUE hMeas hcoeff,?_⟩
  have hb := norm_unitBall_functionalInverse_le hUE hMeas hcoeff
  have hB : metricDensityBudget K ≠ 0 := (show 0 < metricDensityBudget K by unfold metricDensityBudget; positivity).ne'
  have heq : 5/((metricDensityBudget K)⁻¹*K⁻¹) = 5*metricDensityBudget K*K := by field_simp
  rwa [heq] at hb

/-- Uniform weak Dirichlet inverse bound for every actual first-metric normal pullback. -/
theorem uniform_actual_normal_dirichlet_inverse {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand
          (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) x) 0 0)
          ⊤ ((volume : Measure X).restrict ballOpens),
        IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff) ∧
        ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)‖ ≤
          5*metricDensityBudget (4*K^2)*(4*K^2) := by
  obtain ⟨η,hη,hEll⟩ := uniform_enlarged_framed_normal_elliptic hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hG := hEll floor hf ε hε hSmall d hd y hy d.g₁ (by simp)
  exact hG.unitBall_dirichlet_data (by nlinarith)

end ShrinkingSpheres
