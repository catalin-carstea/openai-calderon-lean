module

public import Proof.CalderonN.HarmonicTaylorApproximation
public import Proof.CalderonN.ProductInteriorPointwise

import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.CrossTensor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

public section

set_option maxHeartbeats 2000000

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open LocalMetricExtension (integral_sq_eq_norm_sq)

private theorem exists_bounded_productL2 {A B : Set (X dim)} (hA : IsOpen A) (hB : IsOpen B)
    (hAf : (volume : Measure (X dim)) A ≠ ⊤) (hBf : (volume : Measure (X dim)) B ≠ ⊤)
    {F : (X dim) × (X dim) → ℝ} (hF : ContinuousOn F (A ×ˢ B)) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ q ∈ A ×ˢ B, |F q| ≤ M) :
    let μ := ((volume : Measure (X dim)).restrict A).prod ((volume : Measure (X dim)).restrict B)
    ∃ Q : ChartProductL2 A B, (Q : (X dim) × (X dim) → ℝ) =ᵐ[μ] F ∧ ‖Q‖ ≤ Real.sqrt (μ.real univ) * M := by
  let μ := ((volume : Measure (X dim)).restrict A).prod ((volume : Measure (X dim)).restrict B)
  let _ : IsFiniteMeasure ((volume : Measure (X dim)).restrict A) := isFiniteMeasure_restrict.mpr hAf
  let _ : IsFiniteMeasure ((volume : Measure (X dim)).restrict B) := isFiniteMeasure_restrict.mpr hBf
  have hmeas : AEStronglyMeasurable F μ := by
    rw [show μ = ((volume : Measure (X dim)).prod volume).restrict (A ×ˢ B) from Measure.prod_restrict A B]
    exact hF.aestronglyMeasurable (hA.prod hB).measurableSet
  have hμ : ∀ᵐ q ∂μ, q ∈ A ×ˢ B := by
    rw [show μ = ((volume : Measure (X dim)).prod volume).restrict (A ×ˢ B) from Measure.prod_restrict A B]
    exact ae_restrict_mem (hA.prod hB).measurableSet
  have hLp : MemLp F 2 μ := MemLp.of_bound hmeas M
    (hμ.mono fun q hq => by simpa only [Real.norm_eq_abs] using hbound q hq)
  let Q := hLp.toLp F
  have hRep : (Q : (X dim) × (X dim) → ℝ) =ᵐ[μ] F := MemLp.coeFn_toLp hLp
  refine ⟨Q,hRep,?_⟩
  have hInt : Integrable (fun q => (F q)^2) μ := hLp.integrable_sq
  have hCap : ‖Q‖^2 ≤ (Real.sqrt (μ.real univ) * M)^2 := by
    calc
      _ = ∫ q, (Q q)^2 ∂μ := (integral_sq_eq_norm_sq Q).symm
      _ = ∫ q, (F q)^2 ∂μ := integral_congr_ae (hRep.mono fun q hq => congrArg (fun p : ℝ => p^2) hq)
      _ ≤ ∫ _, M^2 ∂μ := integral_mono_ae hInt (integrable_const _)
        (hμ.mono fun q hq => by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound q hq) 2)
      _ = _ := by
        rw [integral_const,smul_eq_mul,mul_pow,Real.sq_sqrt (measureReal_nonneg : 0 ≤ μ.real univ)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hM)).mp hCap

/-- A bounded pair of observed arms extends into the output with a
common bound on every compact subrectangle of the output. -/
theorem exists_uniform_bounded_productCross
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J)
    {D₁ D₂ S₁ S₂ O₁ O₂ K₁ K₂ : Set (X dim)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hD₁c : IsConnected D₁) (hD₂c : IsConnected D₂)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (hS₁ne : S₁.Nonempty) (hS₂ne : S₂.Nonempty)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    (hSc₁ : IsCompact (closure S₁)) (hScD₁ : closure S₁ ⊆ D₁) (hSD₂ : S₂ ⊆ D₂)
    (hOD₁ : O₁ ⊆ D₁) (hOD₂ : O₂ ⊆ D₂)
    (hDc₁ : IsCompact (closure D₁)) (hDc₂ : IsCompact (closure D₂))
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hKO₁ : K₁ ⊆ O₁) (hKO₂ : K₂ ⊆ O₂)
    {g₁ g₂ : P → (MetricField dim)}
    (hg₁ : ∀ p ∈ J, SmoothMetric D₁ (g₁ p)) (hg₂ : ∀ p ∈ J, SmoothMetric D₂ (g₂ p))
    (ha₁ : ∀ i j, ContDiffOn ℝ ∞ (fun q : P × (X dim) => divergenceCoeff (g₁ q.1) q.2 i j)
      ((univ : Set P) ×ˢ D₁))
    (ha₂ : ∀ i j, ContDiffOn ℝ ∞ (fun q : P × (X dim) => divergenceCoeff (g₂ q.1) q.2 i j)
      ((univ : Set P) ×ˢ D₂))
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1) (hmargin : 0 < γ₁+γ₂-1)
    (hI₁ : ∀ p (hp : p ∈ J), HarmonicInterpolation hD₁ (hg₁ p hp)
      (subset_closure.trans hScD₁) hOD₁ C₁ γ₁)
    (hI₂ : ∀ p (hp : p ∈ J), HarmonicInterpolation hD₂ (hg₂ p hp) hSD₂ hOD₂ C₂ γ₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ (F : (X dim) × (X dim) → ℝ) (M : ℝ), 0 ≤ M →
      ProductSolutionOn (g₁ p) (g₂ p) (D₁ ×ˢ S₂) F →
      ProductSolutionOn (g₁ p) (g₂ p) (S₁ ×ˢ D₂) F →
      (∀ q ∈ (D₁ ×ˢ S₂) ∪ (S₁ ×ˢ D₂), |F q| ≤ M) →
      ∃ G, ProductSolutionOn (g₁ p) (g₂ p) (O₁ ×ˢ O₂) G ∧
        EqOn G F (O₁ ×ˢ (O₂ ∩ S₂)) ∧ EqOn G F ((O₁ ∩ S₁) ×ˢ O₂) ∧
        ∀ q ∈ K₁ ×ˢ K₂, |G q| ≤ C*M := by
  have hSD₁ : S₁ ⊆ D₁ := subset_closure.trans hScD₁
  obtain ⟨s,hs⟩ := exists_nat_gt ((dim : ℝ)/(γ₁+γ₂-1))
  have hs' : (dim : ℝ) < (s : ℝ)*(γ₁+γ₂-1) := (div_lt_iff₀ hmargin).mp hs
  let metric₁ (p : J) := g₁ (p : P)
  have hmetric₁ (p : J) : SmoothMetric D₁ (metric₁ p) := hg₁ p p.property
  obtain ⟨B,N,A₀,hApp⟩ := exists_uniform_counted_harmonic_restrictionApprox
    hD₁ hmetric₁ (fun p => harmonicInteriorJets_of_smoothMetric hD₁ (hmetric₁ p))
    (fun K hK hKD k => by
      obtain ⟨L,hL,h⟩ := exists_uniform_harmonic_interior_jet_bound hJ hD₁ hg₁ ha₁ hK hKD k
      exact ⟨L,hL,fun p => h p p.property⟩)
    hS₁.measurableSet hSc₁ subset_closure hScD₁ s
  obtain ⟨A,hA,hCross⟩ := exists_uniform_smooth_crossExtension s N A₀ B C₁ C₂ γ₁ γ₂
    hC₁ hC₂ hγ₂ hγ₂' hmargin hs'
  obtain ⟨D,hD,hPoint⟩ := exists_uniform_product_harmonic_pointwise_bound hJ hO₁ hO₂ hK₁ hK₂ hKO₁ hKO₂
    (fun p hp => smoothMetric_restrict (hg₁ p hp) hOD₁) (fun p hp => smoothMetric_restrict (hg₂ p hp) hOD₂)
    (fun i j => (ha₁ i j).mono (prod_mono Subset.rfl hOD₁))
    (fun i j => (ha₂ i j).mono (prod_mono Subset.rfl hOD₂))
  let μ₁ := ((volume : Measure (X dim)).restrict D₁).prod ((volume : Measure (X dim)).restrict S₂)
  let μ₂ := ((volume : Measure (X dim)).restrict S₁).prod ((volume : Measure (X dim)).restrict D₂)
  let V := max (Real.sqrt (μ₁.real univ)) (Real.sqrt (μ₂.real univ))
  have hV : 0 ≤ V := (Real.sqrt_nonneg _).trans (le_max_left _ _)
  refine ⟨D*A*V,by positivity,?_⟩
  intro p hp F M hM hFa hFb hMbound
  have hfin₁ : (volume : Measure (X dim)) D₁ ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hDc₁.measure_lt_top).ne
  have hfin₂ : (volume : Measure (X dim)) D₂ ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hDc₂.measure_lt_top).ne
  have hfinSa : (volume : Measure (X dim)) S₁ ≠ ⊤ := ne_top_of_le_ne_top hfin₁ (measure_mono hSD₁)
  have hfinSb : (volume : Measure (X dim)) S₂ ≠ ⊤ := ne_top_of_le_ne_top hfin₂ (measure_mono hSD₂)
  obtain ⟨q₁,hq₁,hq₁b⟩ := exists_bounded_productL2 hD₁ hS₂ hfin₁ hfinSb hFa.1.continuousOn hM
    (fun q hq => hMbound q (Or.inl hq))
  obtain ⟨q₂,hq₂,hq₂b⟩ := exists_bounded_productL2 hS₁ hD₂ hfinSa hfin₂ hFb.1.continuousOn hM
    (fun q hq => hMbound q (Or.inr hq))
  have h₁ : ‖q₁‖ ≤ V*M := hq₁b.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM)
  have h₂ : ‖q₂‖ ≤ V*M := hq₂b.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)
  obtain ⟨Q,G,hG,hQ,hGrep,hAgree₁,hAgree₂⟩ := hCross hD₁ hD₂ hD₁c hD₂c hS₁ hS₂ hS₁ne hS₂ne
    hO₁ hO₂ hSD₁ hSD₂ hOD₁ hOD₂ (hg₁ p hp) (hg₂ p hp) hfin₂
    (harmonicInteriorJets_of_smoothMetric hO₁ (smoothMetric_restrict (hg₁ p hp) hOD₁))
    (harmonicInteriorJets_of_smoothMetric hO₂ (smoothMetric_restrict (hg₂ p hp) hOD₂))
    (hApp ⟨p,hp⟩) (hI₁ p hp) (hI₂ p hp) q₁ q₂ F hq₁ hq₂ hFa hFb (V*M) (mul_nonneg hV hM) h₁ h₂
  refine ⟨G,hG,hAgree₁,hAgree₂,fun q hq => ?_⟩
  calc
    _ ≤ D*‖Q‖ := hPoint p hp Q G hG hGrep q hq
    _ ≤ D*(A*(V*M)) := mul_le_mul_of_nonneg_left hQ hD
    _ = _ := by ring

end CalderonN
