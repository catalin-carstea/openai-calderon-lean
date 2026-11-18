import Proof.PhysicalFirstCommutatorMeasurability
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

theorem PhysicalFirstCommutatorPacket.integral_density_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {CF CT CB CS : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (hCS : 0 ≤ CS) {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius) (hφ : Test Y d.γ d.frame φ) :
    IntegrableOn (D.firstCommutatorDensity W.commLow) Y ∧
      |∫ y in Y,D.firstCommutatorDensity W.commLow y| ≤ (9*CS)*ε*energySq Y d.γ d.frame d.radius φ := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y :=
    fun j => (hd.1.2.2.2.2.2.2.1 j).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖D.firstCommutatorDensity W.commLow y‖ ≤
      ((9*CS)*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact D.abs_firstCommutatorDensity_le hFrame W.commLow hCS hε hε1 hy
      (hf.trans (hd.2.2.2.2.1.2 y hy).2.1) (fun i j => W.comm_bound i j y hy)
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul ((9*CS)*ε)
  refine ⟨hDom.mono' (W.firstCommutatorDensity_aestronglyMeasurable hY hΩ hd (zero_lt_one.trans_le hK) D) hBound,?_⟩
  have hIntegral := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hIntegral
end ShrinkingSpheres
