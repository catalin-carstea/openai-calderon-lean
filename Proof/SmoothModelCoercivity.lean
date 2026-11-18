import Proof.FullEnergyLimit
import Proof.ModelOutputLimits
import Proof.UniformAngularCoercivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The same uniform four-term estimate holds for every smooth compact mean-zero test,
    with the raising and lowering outputs defined by the closed angular operators. -/
theorem Background.energySq_smooth_model_coercive {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hsub : Y ⊆ Ω) {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (hbg : Background Ω K M g g₁ g₂ e)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : backgroundCoercivityFloor hm K M c₀ ≤ floor)
    {φ : Field} (hφ : Test Y g e φ) (E : HarmonicTestExpansion Y g e φ) (D : AngularModelData E r) :
    backgroundModeCoercivityConstant c₀ * energySq Y g e r φ ≤ D.raisingSquare - D.loweringSquare := by
  have hE : Elliptic Y K g := ⟨fun i j => (hbg.1.1 i j).mono hsub,fun y hy => hbg.1.2 y (hsub hy)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y := fun i => (hbg.2.2.2.2.2.2.1 i).mono hsub
  have hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0 :=
    fun y hy => hbg.2.2.2.2.2.2.2 y (hsub hy)
  have hf : 1 ≤ floor := (backgroundCoercivityFloor_ge_one hm K M c₀).trans hfloor
  have henergy := (D.tendsto_energySq_partialField hY hE hK he hframe hp hf hφ).const_mul
    (backgroundModeCoercivityConstant c₀)
  have hR := D.tendsto_outputSq_finiteRaised hY hE hK he hframe hφ.1
  have hL := D.tendsto_outputSq_finiteLowered hY hE hK he hframe hφ.1
  apply le_of_tendsto_of_tendsto' henergy (hR.sub hL)
  intro n
  exact hbg.energySq_finite_angular_coercive hY hΩ hsub hK hm hp hc₀ hfloor (Finset.range n) id
    (fun i hi j hj hij => hij) E.basis (fun k _ j => (E.basisHarmonic k j).1)
    (fun k _ j => (E.basisHarmonic k j).2) E.realCoefficients E.imagCoefficients
    (fun k _ => E.realSmooth k) (fun k _ => E.imagSmooth k)
    (fun k _ => E.real_compact k) (fun k _ => E.imag_compact k)
    (fun k _ => (E.realSupport k).trans E.supportSubset) (fun k _ => (E.imagSupport k).trans E.supportSubset)

/-- All witnesses in the smooth model estimate are constructed from the actual test and
    admissible radius; no finite angular support hypothesis is imposed. -/
theorem Background.exists_coercive_smooth_model {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hsub : Y ⊆ Ω) {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (hbg : Background Ω K M g g₁ g₂ e)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : backgroundCoercivityFloor hm K M c₀ ≤ floor)
    {φ : Field} (hφ : Test Y g e φ) :
    ∃ (E : HarmonicTestExpansion Y g e φ) (D : AngularModelData E r),
      backgroundModeCoercivityConstant c₀ * energySq Y g e r φ ≤ D.raisingSquare - D.loweringSquare := by
  have hE : Elliptic Y K g := ⟨fun i j => (hbg.1.1 i j).mono hsub,fun y hy => hbg.1.2 y (hsub hy)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y := fun i => (hbg.2.2.2.2.2.2.1 i).mono hsub
  have hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0 :=
    fun y hy => hbg.2.2.2.2.2.2.2 y (hsub hy)
  obtain ⟨E⟩ := hφ.exists_harmonicTestExpansion hY e he hframe
  obtain ⟨D⟩ := exists_angularModelData hY hE hK e he hframe hφ.1 E r
    (hp.1.log (fun y hy => (hp.2 y hy).1.ne'))
  exact ⟨E,D,hbg.energySq_smooth_model_coercive hY hΩ hsub hK hm hp hc₀ hfloor hφ E D⟩

end ShrinkingSpheres
