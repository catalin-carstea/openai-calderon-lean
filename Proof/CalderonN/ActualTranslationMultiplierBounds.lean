module

public import Proof.CalderonN.SupportedSphereMultiplierGerms

public import Proof.CalderonN.ActualCenterCorrectionMultiplierBounds

import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

/-! Bounds for the leading coordinate translation multiplier on the
actual supported sphere family. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

@[expose] def actualTranslationMultiplierDatum (d : Data dim) (i : I dim) (x : X dim) : SmoothData dim :=
  smoothVelocityNormal (smoothConstantVelocity (frameCoordinatesL d.γ x (d.frame x) (axis i)))

theorem uniform_actual_translationMultiplier_germs
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,∀ d : Data dim,Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) → ∀ i : I dim,
        let F := supportedSphereMultiplierFamily (fun y (_ : y ∈ Y) => actualTranslationMultiplierDatum d i y)
        ∃ hF : SmoothSupportedTraceFiberRegular Y F, ∀ x ∈ Y,
          SupportedSphereMultiplierGerm (fun y (_ : y ∈ Y) => actualTranslationMultiplierDatum d i y)
            x (beta d.γ d.radius x) C := by
  obtain ⟨C₀,hC₀,hCof⟩ := uniform_frameCoordinatesL_jets hΩ 4 hm K hK M
  let A := (2:ℝ)^4*‖innerSL ℝ (E:=X dim)‖*(24*C₀)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A,hA,?_⟩
  intro floor hFloor ε d hd hFrame i
  dsimp only
  let E := X dim
  let F₀ (x : E) := frameCoordinatesL d.γ x (d.frame x)
  let F₁ (x : E) := F₀ x (axis i)
  let m (x : E) (_ : x ∈ Y) := actualTranslationMultiplierDatum d i x
  have hF₀ (x : E) (hx : x ∈ Y) := hCof hd.1 hFrame x (hSub hx)
  have hF₁ (x : E) (hx : x ∈ Y) : LocalSmoothJetBudget F₁ x 4 C₀ := by
    let J := ContinuousLinearMap.apply ℝ E (axis i)
    have hJ : ‖J‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro T
      rw [one_mul]
      exact (T.le_opNorm _).trans_eq (by rw [norm_axis,mul_one])
    exact ((hF₀ x hx).linear_postcomp J).enlarge
      ((mul_le_mul_of_nonneg_right hJ hC₀).trans_eq (one_mul _))
  have hS : ContDiffOn ℝ ∞ F₁ Y := fun x hx => (hF₁ x hx).smooth.contDiffWithinAt
  let J (p : E × E) := ⟪p.2,F₁ p.1⟫_ℝ
  have hReg : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m) := by
    apply supportedSphereMultiplierFamily_regular hY
    intro x hx
    refine ⟨Y,J,hY,hx,subset_rfl,contDiff_snd.contDiffOn.inner ℝ
      (hS.comp contDiff_fst.contDiffOn (fun _ h => h.1)),?_⟩
    intro y hy hyY z hz
    rfl
  refine ⟨hReg,?_⟩
  intro x hx
  let β := beta d.γ d.radius x
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  obtain ⟨g,hg,hEq⟩ := exists_global_smooth_germ_of_open F₁ hY hS hx
  let p (q : E × E) := ⟪q.2,g q.1⟫_ℝ
  have hp : ContDiff ℝ ∞ p := contDiff_snd.inner ℝ (hg.comp contDiff_fst)
  obtain ⟨U,hU,hOpen,hxU⟩ := _root_.mem_nhds_iff.mp (hEq.and (hY.mem_nhds hx))
  refine ⟨U,p,hOpen,hxU,fun y hy => (hU hy).2,hp,?_,?_⟩
  · intro y hy hyY z hz
    change ⟪z,g y⟫_ℝ = ⟪z,F₁ y⟫_ℝ
    rw [(hU hy).1]
  · intro z hz
    have hgJ := (hF₁ x hx).congr_germ hEq
    have hChart := localSmoothJetBudget_scaled_chart hβ hgJ.smooth (C:=C₀) (N:=4) (fun n hn =>
      (hgJ.bound n hn).trans (le_mul_of_one_le_right hC₀ (one_le_pow₀ hβ)))
    let K₁ := ContinuousLinearMap.fst ℝ E E
    have hK₁ : ‖K₁‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro q
      rw [one_mul]
      exact norm_fst_le q
    have hG : LocalSmoothJetBudget (fun q : E × E => g (x+β⁻¹ • q.1)) 0 4 (24*C₀) := by
      have h : LocalSmoothJetBudget (fun v : E => g (x+β⁻¹ • v)) (K₁ 0) 4 C₀ := by
        rw [map_zero]; exact hChart
      change LocalSmoothJetBudget ((fun v : E => g (x+β⁻¹ • v)) ∘ K₁) 0 4 (24*C₀)
      simpa [max_eq_left hK₁,Nat.factorial] using h.linear_precomp K₁ (0:E × E)
    have hz' : ‖z+(0:E × E).2‖ ≤ 1 := by simpa using mem_closedBall_zero_iff.mp hz
    simpa only [A,mul_one] using hG.sphere_coordinate_inner hz'

theorem uniform_actual_translationMultiplier_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 0 < K) (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f,B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,∀ d : Data dim,Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) → ∀ i : I dim,
        let F := supportedSphereMultiplierFamily (fun y (_ : y ∈ Y) => actualTranslationMultiplierDatum d i y)
        ∃ hF : SmoothSupportedTraceFiberRegular Y F, ∀ x ∈ Y,
          SmoothSupportedTraceCoefficientBounds hn B hY x (beta d.γ d.radius x) 0 C F hF := by
  obtain ⟨A,hA,hG⟩ := uniform_actual_translationMultiplier_germs hY hΩ hSub hm K ρ c₀ M Cj hK
  obtain ⟨C,hC,hLift⟩ := supportedSphereMultiplier_bounds_of_germ (Y:=Y) hn B hB hFin A hA
  refine ⟨C,hC,?_⟩
  intro floor hFloor ε d hd hf i
  obtain ⟨hF,h⟩ := hG floor hFloor ε d hd hf i
  refine ⟨hF,?_⟩
  intro x hx
  exact hLift hY x hx _ (zero_lt_one.trans_le (hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1)) _ hF (h x hx)

end CalderonN
