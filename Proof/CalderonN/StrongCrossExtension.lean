module

public import Proof.CalderonN.CrossNormalConvergence
public import Proof.CalderonN.CrossExtension

import Proof.CalderonN.ClassicalInteriorJets
import Proof.CalderonN.HarmonicTaylorApproximation
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open LocalMetricExtension

/-- The two continuous representatives of a product-measure class agree
pointwise on an open rectangle. -/
theorem eqOn_open_rectangle_of_ae {D₁ D₂ : Set (X dim)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    {F G : (X dim) × (X dim) → ℝ} (hF : ContinuousOn F (D₁ ×ˢ D₂)) (hG : ContinuousOn G (D₁ ×ˢ D₂))
    (heq : F =ᵐ[((volume : Measure (X dim)).restrict D₁).prod ((volume : Measure (X dim)).restrict D₂)] G) :
    EqOn F G (D₁ ×ˢ D₂) := by
  rw [Measure.prod_restrict] at heq
  exact Measure.eqOn_open_of_ae_eq heq (hD₁.prod hD₂) hF hG

private theorem ProductSolutionOn.harmonic_first_slice {D S : Set (X dim)} (_hD : IsOpen D)
    {g₁ g₂ : (MetricField dim)} {F : (X dim) × (X dim) → ℝ} (h : ProductSolutionOn g₁ g₂ (D ×ˢ S) F)
    {y : (X dim)} (hy : y ∈ S) : Harmonic D g₁ (fun x => F (x,y)) :=
  ⟨h.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => ⟨hx,hy⟩),
    fun x hx => h.2.1 (x,y) ⟨hx,hy⟩⟩

private theorem ProductSolutionOn.harmonic_second_slice {D S : Set (X dim)} (_hD : IsOpen D)
    {g₁ g₂ : (MetricField dim)} {F : (X dim) × (X dim) → ℝ} (h : ProductSolutionOn g₁ g₂ (S ×ˢ D) F)
    {x : (X dim)} (hx : x ∈ S) : Harmonic D g₂ (fun y => F (x,y)) :=
  ⟨h.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => ⟨hx,hy⟩),
    fun y hy => h.2.2 (x,y) ⟨hx,hy⟩⟩

/-- The actual two-arm series gives a smooth solution on the output
rectangle with pointwise agreement on both overlaps. -/
theorem exists_uniform_smooth_crossExtension (s N A₀ : ℕ) (B C₁ C₂ γ₁ γ₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1)
    (hmargin : 0 < γ₁ + γ₂ - 1) (hs : (dim : ℝ) < s * (γ₁ + γ₂ - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X dim)}
      (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hc₁ : IsConnected D₁) (hc₂ : IsConnected D₂)
      (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty)
      (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
      (hS₁D₁ : S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂) (hO₁D₁ : O₁ ⊆ D₁) (hO₂D₂ : O₂ ⊆ D₂)
      {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric D₁ g₁) (hg₂ : SmoothMetric D₂ g₂)
      (hfinite : (volume : Measure (X dim)) D₂ ≠ ⊤)
      (hjetO₁ : HarmonicInteriorJets O₁ g₁) (hjetO₂ : HarmonicInteriorJets O₂ g₂)
      (happrox : HasRestrictionApprox hD₁ hg₁ hS₁D₁ s N A₀ B)
      (hfirst : HarmonicInterpolation hD₁ hg₁ hS₁D₁ hO₁D₁ C₁ γ₁)
      (hsecond : HarmonicInterpolation hD₂ hg₂ hS₂D₂ hO₂D₂ C₂ γ₂)
      (q₁ : ChartProductL2 (d := dim) D₁ S₂) (q₂ : ChartProductL2 (d := dim) S₁ D₂) (F : (X dim) × (X dim) → ℝ)
      (hq₁ : (q₁ : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict D₁).prod ((volume : Measure (X dim)).restrict S₂)] F)
      (hq₂ : (q₂ : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict S₁).prod ((volume : Measure (X dim)).restrict D₂)] F)
      (hF₁ : ProductSolutionOn g₁ g₂ (D₁ ×ˢ S₂) F)
      (hF₂ : ProductSolutionOn g₁ g₂ (S₁ ×ˢ D₂) F)
      (M : ℝ) (hM : 0 ≤ M) (hm₁ : ‖q₁‖ ≤ M) (hm₂ : ‖q₂‖ ≤ M),
      ∃ Q : ChartProductL2 O₁ O₂, ∃ G : (X dim) × (X dim) → ℝ,
        ProductSolutionOn g₁ g₂ (O₁ ×ˢ O₂) G ∧ ‖Q‖ ≤ C * M ∧
        (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict O₁).prod ((volume : Measure (X dim)).restrict O₂)] G ∧
        EqOn G F (O₁ ×ˢ (O₂ ∩ S₂)) ∧ EqOn G F ((O₁ ∩ S₁) ×ˢ O₂) := by
  obtain ⟨C,hC,hcross⟩ := exists_uniform_weak_crossExtension s N A₀ B C₁ C₂ γ₁ γ₂
    hC₁ hC₂ hγ₂ hγ₂' hmargin hs
  refine ⟨C,hC,?_⟩
  intro D₁ D₂ S₁ S₂ O₁ O₂ hD₁ hD₂ hc₁ hc₂ hS₁ hS₂ hne₁ hne₂ hO₁ hO₂
    hS₁D₁ hS₂D₂ hO₁D₁ hO₂D₂ g₁ g₂ hg₁ hg₂ hfinite hjetO₁ hjetO₂
    happ hfirst hsecond q₁ q₂ F hq₁ hq₂ hF₁ hF₂ M hM hm₁ hm₂
  obtain ⟨Q,_,hQ,hleft,hright,ι,hcnt,a,b,habs,hser⟩ :=
    hcross hD₁ hD₂ hc₁ hc₂ hS₁ hS₂ hne₁ hne₂ hO₁ hO₂ hS₁D₁ hS₂D₂ hO₁D₁ hO₂D₂ hg₁ hg₂
      hfinite happ hfirst hsecond q₁ q₂ F hq₁ hq₂
      (fun _ hy => hF₁.harmonic_first_slice hD₁ hy)
      (fun _ hx => hF₂.harmonic_second_slice hD₂ hx) M hM hm₁ hm₂
  let _ : Countable ι := hcnt
  obtain ⟨G,hG,hGq⟩ := exists_smooth_productSeries hO₁ hO₂ (smoothMetric_restrict hg₁ hO₁D₁)
    (smoothMetric_restrict hg₂ hO₂D₂) hjetO₁ hjetO₂ a b habs hser
  have hle₁ := Measure.restrict_mono_set (volume : Measure (X dim)) (inter_subset_left (s := O₁) (t := S₁))
  have hle₂ := Measure.restrict_mono_set (volume : Measure (X dim)) (inter_subset_left (s := O₂) (t := S₂))
  refine ⟨Q,G,hG,hQ,hGq,?_,?_⟩
  · exact eqOn_open_rectangle_of_ae hO₁ (hO₂.inter hS₂)
      (hG.1.continuousOn.mono (prod_mono Subset.rfl inter_subset_left))
      (hF₁.1.continuousOn.mono (prod_mono hO₁D₁ inter_subset_right))
      ((hGq.filter_mono (ae_mono (Measure.prod_mono le_rfl hle₂))).symm.trans hleft)
  · exact eqOn_open_rectangle_of_ae (hO₁.inter hS₁) hO₂
      (hG.1.continuousOn.mono (prod_mono inter_subset_left Subset.rfl))
      (hF₂.1.continuousOn.mono (prod_mono inter_subset_right hO₂D₂))
      ((hGq.filter_mono (ae_mono (Measure.prod_mono hle₁ le_rfl))).symm.trans hright)

/-- The actual cross extends whenever its two harmonic interpolations
have a positive exponent margin. The approximation order is chosen
after the exponents and is realized by interior Taylor polynomials. -/
theorem exists_productSolutionOn_cross_of_interpolation
    {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X dim)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hc₁ : IsConnected D₁) (hc₂ : IsConnected D₂)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hO₁D₁ : O₁ ⊆ D₁) (hO₂D₂ : O₂ ⊆ D₂)
    (hSc₁ : IsCompact (closure S₁)) (hSD₁ : closure S₁ ⊆ D₁) (hSD₂ : S₂ ⊆ D₂)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric D₁ g₁) (hg₂ : SmoothMetric D₂ g₂)
    (hfinite : (volume : Measure (X dim)) D₂ ≠ ⊤)
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1)
    (hγ : 0 < γ₁+γ₂-1)
    (hfirst : HarmonicInterpolation hD₁ hg₁ (subset_closure.trans hSD₁) hO₁D₁ C₁ γ₁)
    (hsecond : HarmonicInterpolation hD₂ hg₂ hSD₂ hO₂D₂ C₂ γ₂)
    {F : (X dim) × (X dim) → ℝ}
    (hM₁ : MemLp F 2 (((volume : Measure (X dim)).restrict D₁).prod ((volume : Measure (X dim)).restrict S₂)))
    (hM₂ : MemLp F 2 (((volume : Measure (X dim)).restrict S₁).prod ((volume : Measure (X dim)).restrict D₂)))
    (hF₁ : ProductSolutionOn g₁ g₂ (D₁ ×ˢ S₂) F)
    (hF₂ : ProductSolutionOn g₁ g₂ (S₁ ×ˢ D₂) F) :
    ∃ G : (X dim) × (X dim) → ℝ, ProductSolutionOn g₁ g₂ (O₁ ×ˢ O₂) G ∧
      EqOn G F (O₁ ×ˢ (O₂ ∩ S₂)) ∧ EqOn G F ((O₁ ∩ S₁) ×ˢ O₂) := by
  obtain ⟨s,hs⟩ := exists_nat_gt ((dim : ℝ)/(γ₁+γ₂-1))
  obtain ⟨B,N,A₀,happrox⟩ := exists_counted_harmonic_restrictionApprox hD₁ hg₁
    (harmonicInteriorJets_of_smoothMetric hD₁ hg₁) hS₁.measurableSet hSc₁ subset_closure hSD₁ s
  obtain ⟨C,hC,hcross⟩ := exists_uniform_smooth_crossExtension s N A₀ B C₁ C₂ γ₁ γ₂
    hC₁ hC₂ hγ₂ hγ₂' hγ ((div_lt_iff₀ hγ).mp hs)
  let q₁ := hM₁.toLp F
  let q₂ := hM₂.toLp F
  obtain ⟨Q,G,hG,_,_,hLeft,hRight⟩ := hcross hD₁ hD₂ hc₁ hc₂ hS₁ hS₂ hne₁ hne₂ hO₁ hO₂
    (subset_closure.trans hSD₁) hSD₂ hO₁D₁ hO₂D₂ hg₁ hg₂ hfinite
    (harmonicInteriorJets_of_smoothMetric hO₁ (smoothMetric_restrict hg₁ hO₁D₁))
    (harmonicInteriorJets_of_smoothMetric hO₂ (smoothMetric_restrict hg₂ hO₂D₂))
    happrox hfirst hsecond q₁ q₂ F hM₁.coeFn_toLp hM₂.coeFn_toLp hF₁ hF₂
    (max ‖q₁‖ ‖q₂‖) ((norm_nonneg _).trans (le_max_left _ _)) (le_max_left _ _) (le_max_right _ _)
  exact ⟨G,hG,hLeft,hRight⟩

end CalderonN
