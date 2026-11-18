import Proof.ProductOutputCompletion
import Proof.SmoothModelCoercivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres

structure AngularProductOutputs {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}
    {E : HarmonicTestExpansion Y g e φ} {r : X → ℝ} (D : AngularModelData E r) where
  raising : ProductOutputRealization D.realComponent.raisingOutput D.imagComponent.raisingOutput Y g E.supportSet
  lowering : ProductOutputRealization D.realComponent.loweringOutput D.imagComponent.loweringOutput Y g E.supportSet

namespace AngularModelData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ} {r : X → ℝ}

theorem exists_productOutputs (D : AngularModelData E r) (hY : IsOpen Y)
    (hρ : ContinuousOn (metricDensity g) Y) : Nonempty (AngularProductOutputs D) := by
  obtain ⟨R⟩ := exists_productOutputRealization hY hρ _ _
    D.realComponent.contDiff_raisingOutput D.imagComponent.contDiff_raisingOutput E.supportSet E.compactSupportSet E.supportSubset
    (fun y hy => D.realComponent.raisingOutput_zero hy) (fun y hy => D.imagComponent.raisingOutput_zero hy)
  obtain ⟨L⟩ := exists_productOutputRealization hY hρ _ _
    D.realComponent.contDiff_loweringOutput D.imagComponent.contDiff_loweringOutput E.supportSet E.compactSupportSet E.supportSubset
    (fun y hy => D.realComponent.loweringOutput_zero hy) (fun y hy => D.imagComponent.loweringOutput_zero hy)
  exact ⟨⟨R,L⟩⟩

end AngularModelData

/-- The smooth angular model supplies genuine witnesses for the coercive part of the
    frozen product-space analytic estimates. Their norms and harmonic approximation are exact. -/
theorem Background.exists_coercive_product_outputs {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hsub : Y ⊆ Ω) {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (hbg : Background Ω K M g g₁ g₂ e)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : backgroundCoercivityFloor hm K M c₀ ≤ floor)
    {φ : Field} (hφ : Test Y g e φ) :
    ∃ (E : HarmonicTestExpansion Y g e φ) (D : AngularModelData E r) (O : AngularProductOutputs D),
      backgroundModeCoercivityConstant c₀ * energySq Y g e r φ ≤ ‖O.raising.output‖^2-‖O.lowering.output‖^2 := by
  obtain ⟨E,D,hD⟩ := hbg.exists_coercive_smooth_model hY hΩ hsub hK hm hp hc₀ hfloor hφ
  have hρ : ContinuousOn (metricDensity g) Y :=
    ((hbg.1.contDiffOn_density hK).mono hsub).continuousOn
  obtain ⟨O⟩ := D.exists_productOutputs hY hρ
  refine ⟨E,D,O,?_⟩
  rw [O.raising.normSq,O.lowering.normSq]
  exact hD

end ShrinkingSpheres
