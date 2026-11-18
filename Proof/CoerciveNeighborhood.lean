import Proof.CommonSupportWeakEnergyRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Coercivity persists on an explicit operator-norm neighborhood. -/
theorem isCoercive_of_half_norm_perturbation {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B B0 : E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ) (hα : 0 < α)
    (hLower : ∀ u,α*‖u‖*‖u‖ ≤ B0 u u) (hNear : ‖B-B0‖ ≤ α/2) : IsCoercive B := by
  refine ⟨α/2,by positivity,?_⟩
  intro u
  have hD : |(B-B0) u u| ≤ ‖B-B0‖*‖u‖*‖u‖ := by
    simpa only [Real.norm_eq_abs] using (B-B0).le_opNorm₂ u u
  have hLow := (abs_le.mp hD).1
  change -(‖B-B0‖*‖u‖*‖u‖) ≤ B u u-B0 u u at hLow
  have hBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hNear (norm_nonneg u)) (norm_nonneg u)
  nlinarith only [hLower u,hLow,hBound]

theorem isOpen_setOf_isCoercive {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsOpen {B : E →L[ℝ] E →L[ℝ] ℝ | IsCoercive B} := by
  rw [isOpen_iff_mem_nhds]
  intro B0 h0
  obtain ⟨α,hα,hLower⟩ := h0
  apply Filter.mem_of_superset (Metric.ball_mem_nhds B0 (by positivity : 0 < α/2))
  intro B hB
  exact isCoercive_of_half_norm_perturbation B B0 α hα hLower
    (le_of_lt (by
      have hDist : dist B B0 < α/2 := hB
      exact (_root_.dist_eq_norm B B0) ▸ hDist))

/-- A genuine common-support energy family has a local coercive locus around
    each coercive point, with the same coefficient witnesses. -/
theorem exists_commonSupport_coercive_neighborhood
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0)
    (h0 : IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha 0))) :
    ∃ U : Set ℝ,IsOpen U ∧ (0:ℝ) ∈ U ∧
      ∀ t ∈ U,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha t)) := by
  let B : ℝ → BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ := commonSupportZeroWeakEnergy a ha
  let U := {t : ℝ | IsCoercive (B t)}
  have hU : IsOpen U := (isOpen_setOf_isCoercive (E:=BallH1Zero)).preimage
    (show Continuous B from (contDiff_commonSupportZeroWeakEnergy a ha S hS hz).continuous)
  exact ⟨U,hU,h0,fun _ h => h⟩

end ShrinkingSpheres
