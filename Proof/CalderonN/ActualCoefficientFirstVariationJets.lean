module

public import Proof.CalderonN.ActualFramedCoefficientRemainder

import Proof.CalderonN.FirstDensityJetBounds
import Mathlib.Tactic

/-! The first variation of the same fixed-ball coefficient has uniform
mixed jets, obtained by taking its actual vertical derivative at zero. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def actualFramedCoefficientFirst (d : Data dim) (p : FramedRadialParameter dim) : Mat dim :=
  (firstDensityCenterLinear d p.1.1 p.2) • (1 : Mat dim)

theorem uniform_actual_framedCoefficient_first_jets (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∀ s ∈ Icc (-1:ℝ) 1, ∀ z ∈ closedBall (0:X dim) L,
        LocalSmoothJetBudget (actualFramedCoefficientFirst d) ((y,s),z) N C := by
  let P := FramedRadialParameter dim
  let Q := NormalCoefficientRadialParameter dim
  let X₂ := X dim × X dim
  let V₀ : Q →L[ℝ] X₂ := (ContinuousLinearMap.inl ℝ (X dim) (X dim)).comp (ContinuousLinearMap.fst ℝ _ _)
  let W₀ : Q →L[ℝ] X₂ := (ContinuousLinearMap.inr ℝ (X dim) (X dim)).comp
    ((ContinuousLinearMap.snd ℝ ℝ (X dim)).comp (ContinuousLinearMap.snd ℝ _ _))
  let Ev := (ContinuousLinearMap.apply (E:=X₂) ℝ (Mat dim)).flip
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨η,hη,hGeom⟩ := uniform_actual_normal_radial_segment (Y:=Y) hΩ
    (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ 0 (by norm_num)
  obtain ⟨CIn,hCIn,hIn⟩ := uniform_actual_framedRadialInput_jets
    hΩ hYc N (by omega) K ρ c₀ M Cj hK L
  obtain ⟨CA,hCA,hA⟩ := uniform_actual_firstNormalVelocityCoefficient_jets
    hY hΩ (N+1) hm K ρ c₀ M Cj hK
  let CV := max 1 (‖V₀‖*CIn)
  let CW := ‖W₀‖*CIn
  let D := N.factorial*CA*CV^N
  let C := (2:ℝ)^N*‖Ev‖*D*CW
  have hCV : 1 ≤ CV := le_max_left _ _
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hCA))
    (pow_nonneg (zero_le_one.trans hCV) _)
  have hCW : 0 ≤ CW := mul_nonneg (norm_nonneg _) (zero_le_one.trans hCIn)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)) hD) hCW
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε hε hεη d hd hdFrame y hy s hs z hz
  let p : P := ((y,s),z)
  let F := actualNormalVelocityField d
  let V : P → X₂ := V₀ ∘ actualFramedRadialInput d
  let W : P → X₂ := W₀ ∘ actualFramedRadialInput d
  have hF (x : X dim) (hx : x ∈ Y) : LocalSmoothJetBudget F (x,0) (N+1) CA := by
    have hr := (hd.2.2.2.2.1.2 x hx).1
    have hDisk : (0:X dim) ∈ disk d.γ x (0:ℝ) := by simp [disk,metricPair]
    have h0 := (hGeom floor hf ε hε hεη d hd x hx 0 (by simpa using hr.le) 0 hDisk).2.2 0 (by simp)
    simp only [zero_mul,zero_smul] at h0
    exact hA floor ε d hd hdFrame x hx 0 h0.2.1 h0.2.2.1 h0.2.2.2
  have hInput := hIn floor ε d hd hdFrame y hy s hs z hz
  have hV : LocalSmoothJetBudget V p N CV := (hInput.linear_postcomp V₀).enlarge (le_max_right _ _)
  have hW : LocalSmoothJetBudget W p N CW := hInput.linear_postcomp W₀
  have hD' : LocalSmoothJetBudget (fderiv ℝ F ∘ V) p N D := hV.comp (hF y hy).fderiv hCV
  have hL : LocalSmoothJetBudget (fun q => fderiv ℝ F (V q) (W q)) p N C := by
    have h := hD'.bilinear hW Ev
    exact h
  have hE : (fun q => fderiv ℝ F (V q) (W q)) =ᶠ[𝓝 p] actualFramedCoefficientFirst d := by
    have hU : (fun q : P => q.1.1) ⁻¹' Y ∈ 𝓝 p := (hY.preimage continuous_fst.fst).mem_nhds hy
    filter_upwards [hU] with q hq
    change q.1.1 ∈ Y at hq
    change fderiv ℝ F (q.1.1,0) (0,frameVector d.frame q.1.1 q.2) = _
    exact actualFirstNormalCoefficient_verticalDerivative hn hΩ hd hKp hq q.2
      ((hF q.1.1 hq).smooth.differentiableAt (by simp))
  refine ⟨hL.smooth.congr_of_eventuallyEq hE.symm,fun j hj => ?_⟩
  rw [← (hE.iteratedFDeriv ℝ j).eq_of_nhds]
  exact hL.bound j hj

end CalderonN
