module

public import Proof.CalderonN.ActualRelativeCoefficientFactorization

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.FirstDensityJetBounds
import Proof.CalderonN.AffineNormalizedCenterJets
import Mathlib.Tactic

/-! Compact extensions of the physical relative coefficient jets on a
neighborhood of the fixed closed ball. All bounds concern their germs. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem localSmoothJetBudget_congr (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f g : P → E} {x : P} {N : ℕ} {C : ℝ} (h : LocalSmoothJetBudget f x N C)
    (he : g =ᶠ[𝓝 x] f) : LocalSmoothJetBudget g x N C :=
  ⟨h.smooth.congr_of_eventuallyEq he,fun n hn => by
    rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
    exact h.bound n hn⟩

/-- The two extended coefficients share a compact spatial support and their
affine combination is the genuine coefficient on a physical ball collar. -/
theorem uniform_actual_relativeCoefficient_germs (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C₁ C₂ : ℝ, 0 < η ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∃ (a₁ a₂ : FramedRadialParameter dim → Mat dim) (J : Set (X dim))
        (W : Set (FramedRadialParameter dim)),
        ContDiff ℝ ∞ a₁ ∧ ContDiff ℝ ∞ a₂ ∧ IsCompact J ∧
        (∀ p z, z ∉ J → a₁ (p,z) = 0 ∧ a₂ (p,z) = 0) ∧
        IsOpen W ∧ {(y,(0:ℝ))} ×ˢ closedBall (0:X dim) 1 ⊆ W ∧
        EqOn a₁ (actualRelativeCoefficientFirst d) W ∧
        EqOn a₂ (actualRelativeCoefficientRemainder d (d.radius y)) W ∧
        (∀ p ∈ W, actualFramedCoefficientField d (actualRelativeCoefficientInput (d.radius y) p) =
          1+(d.radius y) • a₁ p+(d.radius y)^2 • a₂ p) ∧
        ∀ z ∈ closedBall (0:X dim) 1,
          LocalSmoothJetBudget a₁ ((y,0),z) N C₁ ∧ LocalSmoothJetBudget a₂ ((y,0),z) N C₂ := by
  obtain ⟨η,C₁,C₂,hη,hC₁,hC₂,hFactor⟩ := uniform_actual_relativeCoefficient_factorization
    hn hY hΩ hYc N hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηG,hηG,hGeom⟩ := uniform_actual_normal_radial_segment_enlarged (Y:=Y)
    hΩ (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ 1 (by norm_num)
  refine ⟨min η ηG,C₁,C₂,lt_min hη hηG,hC₁,hC₂,?_⟩
  intro floor hf ε he hs d hd hdFrame y hy
  let P := FramedRadialParameter dim
  let p₀ : X dim × ℝ := (y,0)
  let r := d.radius y
  let K₀ : Set P := {p₀} ×ˢ closedBall (0:X dim) 1
  let f₁ := actualRelativeCoefficientFirst d
  let f₂ := actualRelativeCoefficientRemainder d r
  have hK₀ : IsCompact K₀ := isCompact_singleton.prod (isCompact_closedBall _ _)
  obtain ⟨hBound,hEq⟩ := hFactor floor hf ε he (hs.trans (min_le_left _ _)) d hd hdFrame
  have hB (q : P) (hq : q ∈ K₀) : LocalSmoothJetBudget f₁ q N C₁ ∧ LocalSmoothJetBudget f₂ q N C₂ := by
    have hq₁ : q.1 = p₀ := hq.1
    have hqEq : q = ((y,0),q.2) := Prod.ext hq₁ rfl
    rw [hqEq]
    exact hBound y hy q.2 (closedBall_subset_closedBall (by norm_num) hq.2)
  let U : Set P := (fun q : P => q.1.1) ⁻¹' Y
  have hU : IsOpen U := hY.preimage continuous_fst.fst
  have hKU : K₀ ⊆ U := by
    intro q hq
    have hq₁ : q.1 = p₀ := hq.1
    change q.1.1 ∈ Y
    rwa [hq₁]
  have hKp := zero_lt_one.trans_le hK
  have hYΩ : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hFrameS : ContDiffOn ℝ ∞ (frameVectorLinear d.frame) Ω := by
    unfold frameVectorLinear
    exact ContDiffOn.sum (fun i _ => ((ContinuousLinearMap.smulRightL ℝ (X dim) (X dim))
      (EuclideanSpace.proj i)).contDiff.comp_contDiffOn (hd.1.2.2.2.2.2.2.1 i))
  have hDensity := hd.1.firstMetricDensityFactor_smooth hKp
  have hLine : ContDiffOn ℝ ∞ (firstDensityCenterLinear d) Ω := by
    change ContDiffOn ℝ ∞ (fun y => centerInverseDensity d y •
      (fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) y).comp (frameVectorLinear d.frame y)) Ω
    exact (hd.1.contDiffOn_centerInverseDensity hKp).smul
      ((hDensity.fderiv_of_isOpen (m:=∞) hΩ (by simp)).clm_comp hFrameS)
  have hProj : MapsTo (fun q : P => q.1.1) U Ω := fun _ hq => hYΩ hq
  have hF₁ : ContDiffOn ℝ ∞ f₁ U := by
    have h := (hLine.comp contDiff_fst.fst.contDiffOn hProj).clm_apply contDiff_snd.contDiffOn
    exact (contDiff_const.add contDiff_fst.snd).contDiffOn.smul (h.smul contDiffOn_const)
  obtain ⟨E,hE,hTube,hF⟩ := smoothNear_actual_firstNormalVelocityCoefficient hΩ hKp hd
  have hF' : ContDiffOn ℝ ∞ (actualNormalVelocityField d) E := hF
  obtain ⟨T,hT,hRay,hTay⟩ := smoothNear_normalRadialTaylorRemainder hE hF'
  let A : P → NormalCoefficientRadialParameter dim :=
    actualFramedRadialInput d ∘ actualRelativeCoefficientInput r
  have hInput : ContDiffOn ℝ ∞ A U := by
    have hFrame := (hFrameS.comp contDiff_fst.fst.contDiffOn hProj).clm_apply contDiff_snd.contDiffOn
    have hVec : ContDiffOn ℝ ∞ (fun q : P => frameVector d.frame q.1.1 q.2) U := by
      simpa only [Function.comp_apply,frameVectorLinear_apply] using hFrame
    exact contDiff_fst.fst.contDiffOn.prodMk
      ((contDiff_const.mul (contDiff_const.add contDiff_fst.snd)).contDiffOn.prodMk hVec)
  let U₂ := U ∩ A ⁻¹' T
  have hU₂ : IsOpen U₂ := hInput.continuousOn.isOpen_inter_preimage hU hT
  have hKU₂ : K₀ ⊆ U₂ := by
    intro q hq
    refine ⟨hKU hq,hRay ?_⟩
    have hq₁ : q.1 = p₀ := hq.1
    have hr := (hd.2.2.2.2.1.2 y hy).1
    let w := frameVector d.frame y q.2
    have hFrameY := hd.1.2.2.2.2.2.2.2 y (hYΩ hy)
    have hw := frameVector_mem_disk d.γ d.frame y q.2 1 hFrameY hq.2
    have hrAbs : |r| ≤ 2*d.radius y := by dsimp only [r]; rw [abs_of_pos hr]; linarith
    obtain ⟨_,_,hG⟩ := hGeom floor hf ε he (hs.trans (min_le_right _ _)) d hd y hy r hrAbs w hw
    intro t ht
    have hAq : A q = (y,(r,w)) := by
      simp only [A,Function.comp_apply,actualFramedRadialInput,actualRelativeCoefficientInput,hq₁,p₀,w,
        add_zero,mul_one]
    rw [hAq]
    exact hTube ⟨hy,(hG t ht).1,((hG t ht).2.2.2).trans_lt (by norm_num)⟩
  have hF₂ : ContDiffOn ℝ ∞ f₂ U₂ :=
    ((contDiff_const.add contDiff_fst.snd).pow 2).contDiffOn.smul
      (hTay.comp (hInput.mono inter_subset_left) (fun _ hq => hq.2))
  obtain ⟨a₁,ha₁,ha₁s,V₁,hV₁,hKV₁,_,hE₁⟩ :=
    exists_contDiff_extension_near_compact hU hK₀ hKU hF₁
  obtain ⟨a₂,ha₂,ha₂s,V₂,hV₂,hKV₂,_,hE₂⟩ :=
    exists_contDiff_extension_near_compact hU₂ hK₀ hKU₂ hF₂
  let J := Prod.snd '' (tsupport a₁ ∪ tsupport a₂)
  have hJ : IsCompact J := (ha₁s.isCompact.union ha₂s.isCompact).image continuous_snd
  let B (q : P) := 2*d.radius q.1.1-|r*(1+q.1.2)|
  have hC : ContinuousOn B U :=
    (continuousOn_const.mul (hd.2.2.2.2.1.1.continuousOn.comp continuous_fst.fst.continuousOn
      (fun _ h => h))).sub ((continuous_const.mul (continuous_const.add continuous_fst.snd)).abs.continuousOn)
  let O := U ∩ B ⁻¹' Ioi 0 ∩ Prod.snd ⁻¹' ball (0:X dim) 2
  have hO : IsOpen O := (hC.isOpen_inter_preimage hU isOpen_Ioi).inter (isOpen_ball.preimage continuous_snd)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hK₀O : K₀ ⊆ O := by
    intro q hq
    have hq₁ : q.1 = p₀ := hq.1
    refine ⟨⟨?_,?_⟩,closedBall_subset_ball (by norm_num) hq.2⟩
    · change q.1.1 ∈ Y
      rw [hq₁]
      exact hy
    · change 0 < 2*d.radius q.1.1-|r*(1+q.1.2)|
      rw [hq₁]
      simp only [p₀,add_zero,mul_one,r,abs_of_pos hr]
      linarith
  let W := (V₁ ∩ V₂) ∩ O
  have hW : IsOpen W := (hV₁.inter hV₂).inter hO
  have hK₀W : K₀ ⊆ W := fun q hq => ⟨⟨hKV₁ hq,hKV₂ hq⟩,hK₀O hq⟩
  refine ⟨a₁,a₂,J,W,ha₁,ha₂,hJ,?_,hW,hK₀W,fun _ hq => hE₁ hq.1.1,fun _ hq => hE₂ hq.1.2,?_,?_⟩
  · intro p z hz
    have hOff₁ : (p,z) ∉ tsupport a₁ := fun h => hz ⟨(p,z),Or.inl h,rfl⟩
    have hOff₂ : (p,z) ∉ tsupport a₂ := fun h => hz ⟨(p,z),Or.inr h,rfl⟩
    exact ⟨image_eq_zero_of_notMem_tsupport hOff₁,image_eq_zero_of_notMem_tsupport hOff₂⟩
  · intro q hq
    have hb : 0 < B q := hq.2.1.2
    have hs₁ : |r*(1+q.1.2)| ≤ 2*d.radius q.1.1 := le_of_lt (sub_pos.mp hb)
    rw [hE₁ hq.1.1,hE₂ hq.1.2]
    exact hEq r q hq.2.1.1 (ball_subset_closedBall hq.2.2) hs₁
  · intro z hz
    have hp : (p₀,z) ∈ K₀ := ⟨mem_singleton _,hz⟩
    have hb := hB (p₀,z) hp
    have he₁ : a₁ =ᶠ[𝓝 (p₀,z)] f₁ := by
      filter_upwards [hV₁.mem_nhds (hKV₁ hp)] with q hq using hE₁ hq
    have he₂ : a₂ =ᶠ[𝓝 (p₀,z)] f₂ := by
      filter_upwards [hV₂.mem_nhds (hKV₂ hp)] with q hq using hE₂ hq
    exact ⟨localSmoothJetBudget_congr _ hb.1 he₁,localSmoothJetBudget_congr _ hb.2 he₂⟩

end CalderonN
