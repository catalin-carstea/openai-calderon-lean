import Proof.WeakDirichletContinuity
import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
open Set MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def centerMetric (g : MetricField) : MetricField := fun _ => g 0

lemma Elliptic.freeze_at_zero {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (h0 : (0:X) ∈ Ω) (Ω' : Set X) : Elliptic Ω' K (centerMetric g) := by
  refine ⟨fun _ _ => contDiffOn_const,?_⟩
  intro x hx
  exact hg.2 0 h0

section Bilinear
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma coercive_bilinear_solution_bound (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u,c*‖u‖*‖u‖ ≤ B u u)
    (ell : StrongDual ℝ V) (u : V) (hu : ∀ v,B u v = ell v) : ‖u‖ ≤ c⁻¹*‖ell‖ := by
  have hb : c*‖u‖*‖u‖ ≤ ‖ell‖*‖u‖ :=
    (hB u).trans ((hu u).le.trans ((le_abs_self _).trans (ell.le_opNorm u)))
  by_cases hZero : u = 0
  · simp only [hZero,norm_zero]; positivity
  · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hZero
    exact (le_inv_mul_iff₀ hc).2 ((mul_le_mul_iff_left₀ hn).mp hb)

/-- Quantitative comparison of any two weak solutions with the same forcing. -/
theorem coercive_bilinear_solution_difference_bound (B B0 : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c) (hB : ∀ u,c*‖u‖*‖u‖ ≤ B u u)
    (hB0 : ∀ u,c*‖u‖*‖u‖ ≤ B0 u u)
    (ell : StrongDual ℝ V) (u u0 : V) (hu : ∀ v,B u v = ell v) (hu0 : ∀ v,B0 u0 v = ell v) :
    ‖u-u0‖ ≤ c⁻¹^2*‖B-B0‖*‖ell‖ := by
  let w := u-u0
  have hEq : B w w = -((B-B0) u0 w) := by
    dsimp only [w]
    simp only [map_sub,_root_.sub_apply,hu,hu0]
    ring
  have hU := coercive_bilinear_solution_bound B0 c hc hB0 ell u0 hu0
  have hOp : |(B-B0) u0 w| ≤ ‖B-B0‖*‖u0‖*‖w‖ := by
    simpa only [Real.norm_eq_abs] using (((B-B0) u0).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right ((B-B0).le_opNorm u0) (norm_nonneg w))
  have hEnergy : c*‖w‖*‖w‖ ≤ ‖B-B0‖*(c⁻¹*‖ell‖)*‖w‖ := by
    have hh := (hB w).trans (le_abs_self (B w w))
    rw [hEq,abs_neg] at hh
    exact (hh.trans hOp).trans (by gcongr)
  by_cases hZero : w = 0
  · change ‖w‖ ≤ _
    rw [hZero,norm_zero]
    positivity
  · have hn : 0 < ‖w‖ := norm_pos_iff.mpr hZero
    have hh := (le_inv_mul_iff₀ hc).2 ((mul_le_mul_iff_left₀ hn).mp hEnergy)
    change ‖w‖ ≤ _
    convert hh using 1 <;> ring

end Bilinear

/-- Fixed-ball weak solution comparison from actual metric coefficient control. -/
theorem Elliptic.unitBall_solution_center_comparison {K : ℝ} {H : MetricField}
    (hEll : Elliptic (Metric.closedBall (0:X) 2) K H) (hK : 1 ≤ K) (q : ℝ) (hq : 0 ≤ q)
    (hDiff : ∀ z ∈ (ballOpens : Set X),∀ i j,
      |principalCoefficient H z i j-principalCoefficient (centerMetric H) z i j| ≤ q)
    (hcoeff : MemLp (fun z => TauCeti.PDE.energyIntegrand (principalCoefficient H z) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (hcoeff0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (principalCoefficient (centerMetric H) z) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (ell : StrongDual ℝ BallH1Zero) (u u0 : BallH1Zero)
    (hu : ∀ v,TauCeti.PDE.energyFormH1L0 hcoeff u v = ell v)
    (hu0 : ∀ v,TauCeti.PDE.energyFormH1L0 hcoeff0 u0 v = ell v) :
    ‖u-u0‖ ≤ 9*(5*metricDensityBudget K*K)^2*q*‖ell‖ := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have h0 : (0:X) ∈ Metric.closedBall (0:X) 2 := by simp
  have hFlat := hEll.freeze_at_zero h0 (Metric.closedBall (0:X) 2)
  have hUE := (hEll.principalCoefficient_tau hK).mono_set unitBall_subset_closedBall_two
  have hUE0 := (hFlat.principalCoefficient_tau hK).mono_set unitBall_subset_closedBall_two
  have hSmooth := hEll.contDiffOn_principalCoefficient hKpos
  have hSmooth0 := hFlat.contDiffOn_principalCoefficient hKpos
  have hMeas : AEStronglyMeasurable (principalCoefficient H) ((volume:Measure X).restrict ballOpens) := (hSmooth.continuousOn.mono unitBall_subset_closedBall_two).aestronglyMeasurable ballOpens.isOpen.measurableSet
  have hMeas0 : AEStronglyMeasurable (principalCoefficient (centerMetric H)) ((volume:Measure X).restrict ballOpens) := (hSmooth0.continuousOn.mono unitBall_subset_closedBall_two).aestronglyMeasurable ballOpens.isOpen.measurableSet
  let c := ((metricDensityBudget K)⁻¹*K⁻¹)/5
  have hc : 0 < c := div_pos hUE.pos (by norm_num)
  have hB := unitBall_zeroDrift_coercivity hUE hMeas hcoeff
  have hB0 := unitBall_zeroDrift_coercivity hUE0 hMeas0 hcoeff0
  have hb := coercive_bilinear_solution_difference_bound
    (TauCeti.PDE.energyFormH1L0 hcoeff) (TauCeti.PDE.energyFormH1L0 hcoeff0) c hc hB hB0 ell u u0 hu hu0
  have hOp := norm_unitBall_energyForm_sub_le hcoeff hcoeff0 q hq hDiff
  have hBudget : metricDensityBudget K ≠ 0 := (show 0 < metricDensityBudget K by unfold metricDensityBudget; positivity).ne'
  have hcInv : c⁻¹ = 5*metricDensityBudget K*K := by dsimp only [c]; field_simp
  have hb' : ‖u-u0‖ ≤ c⁻¹^2*(9*q)*‖ell‖ := hb.trans (by gcongr)
  have hScalar (t : ℝ) : c⁻¹^2*(9*q)*t = 9*(5*metricDensityBudget K*K)^2*q*t := by
    rw [hcInv]
    ring
  exact hb'.trans_eq (hScalar ‖ell‖)

end ShrinkingSpheres
