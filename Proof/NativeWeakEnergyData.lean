import Proof.UniformEllipticWeakEstimates
import Proof.NativeWeakInverseBound
import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- A shared coefficient witness for the native weak inverse and energy bounds. -/
structure NativeWeakEnergyData (a : X → Mat) (C D : ℝ) : Prop where
  coefficient_bound : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
    ⊤ ((volume:Measure X).restrict ballOpens)
  coercive : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) coefficient_bound)
  inverse_bound : ‖nativeCoefficientWeakFunctionalInverse a (fun _ => (0:X)) (fun _ => (0:ℝ)) coefficient_bound‖ ≤ C
  energy_bound : ‖TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) coefficient_bound‖ ≤ D

/-- Uniform native weak operator data from the actual metric ellipticity. -/
theorem Elliptic.nativeWeakEnergyData {K : ℝ} {g : MetricField}
    (hg : Elliptic (Metric.closedBall (0:X) 2) K g) (hK : 1 ≤ K) :
    NativeWeakEnergyData (principalCoefficient g) (5*metricDensityBudget K*K) (metricDensityBudget K*K) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hBpos : 0 < metricDensityBudget K := by unfold metricDensityBudget;positivity
  have hUE := (hg.principalCoefficient_tau hK).mono_set unitBall_subset_closedBall_two
  have hSmooth := hg.contDiffOn_principalCoefficient hKpos
  have hMeas : AEStronglyMeasurable (principalCoefficient g) ((volume:Measure X).restrict ballOpens) :=
    (hSmooth.continuousOn.mono unitBall_subset_closedBall_two).aestronglyMeasurable ballOpens.isOpen.measurableSet
  obtain ⟨hcoeff,hCoercive,hInv,hEnergy⟩ := exists_native_weak_estimates_of_uniformlyElliptic
    (principalCoefficient g) ((metricDensityBudget K)⁻¹*K⁻¹) (metricDensityBudget K*K) hUE hMeas
  refine ⟨hcoeff,hCoercive,hInv.trans_eq ?_,hEnergy⟩
  field_simp

theorem uniform_actual_native_weak_energy_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      NativeWeakEnergyData (principalCoefficient
        (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)))
        (5*metricDensityBudget (4*K^2)*(4*K^2)) (metricDensityBudget (4*K^2)*(4*K^2)) := by
  obtain ⟨η,hη,hE⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hEll := hE floor hf ε hε hSmall d hd y hy d.g₁ (by simp)
  exact hEll.nativeWeakEnergyData (by nlinarith only [hK,sq_nonneg (K-1)])

end ShrinkingSpheres
