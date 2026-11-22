module

public import Proof.CalderonN.AffineChart
public import Proof.CalderonN.GreenCross

import Proof.CalderonN.GreenWeak

public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {n : ℕ} [NeZero n]

@[expose] def separateAffineChart (c₁ c₂ : (X n)) (s : ℝ) (q : (X n) × (X n)) : (X n) × (X n) :=
  (affineChartMap c₁ s q.1, affineChartMap c₂ s q.2)

theorem contDiff_separateAffineChart (c₁ c₂ : (X n)) (s : ℝ) :
    ContDiff ℝ ∞ (separateAffineChart c₁ c₂ s) :=
  ((contDiff_affineChartMap c₁ s).comp contDiff_fst).prodMk
    ((contDiff_affineChartMap c₂ s).comp contDiff_snd)

theorem ProductSolutionOn.separateAffineChart_pullback
    {V : Set ((X n) × (X n))} (hV : IsOpen V) {g₁ g₂ : (MetricField n)}
    (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {F : (X n) × (X n) → ℝ} (hF : ProductSolutionOn g₁ g₂ V F) (c₁ c₂ : (X n)) (s : ℝ) :
    ProductSolutionOn (affineChartMetric g₁ (c₁,s)) (affineChartMetric g₂ (c₂,s))
      (separateAffineChart c₁ c₂ s ⁻¹' V) (F ∘ separateAffineChart c₁ c₂ s) := by
  refine ⟨hF.1.comp (contDiff_separateAffineChart c₁ c₂ s).contDiffOn (fun _ h => h),?_,?_⟩
  · intro q hq
    let U := (fun x : (X n) => (x,affineChartMap c₂ s q.2)) ⁻¹' V
    have hU : IsOpen U := hV.preimage (continuous_id.prodMk continuous_const)
    have hf : ContDiffOn ℝ ∞ (fun x => F (x,affineChartMap c₂ s q.2)) U :=
      hF.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ h => h)
    have h := laplace_affineChart hU ⟨fun i j => (hg₁.1 i j).mono (subset_univ U),fun z _ => hg₁.2 z (mem_univ _)⟩ hf c₁ s hq
    exact h.trans (by rw [show laplace g₁ (fun x => F (x,affineChartMap c₂ s q.2))
      (affineChartMap c₁ s q.1) = 0 from hF.2.1 (separateAffineChart c₁ c₂ s q) hq,mul_zero])
  · intro q hq
    let U := (fun y : (X n) => (affineChartMap c₁ s q.1,y)) ⁻¹' V
    have hU : IsOpen U := hV.preimage (continuous_const.prodMk continuous_id)
    have hf : ContDiffOn ℝ ∞ (fun y => F (affineChartMap c₁ s q.1,y)) U :=
      hF.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
    have h := laplace_affineChart hU ⟨fun i j => (hg₂.1 i j).mono (subset_univ U),fun z _ => hg₂.2 z (mem_univ _)⟩ hf c₂ s hq
    exact h.trans (by rw [show laplace g₂ (fun y => F (affineChartMap c₁ s q.1,y))
      (affineChartMap c₂ s q.2) = 0 from hF.2.2 (separateAffineChart c₁ c₂ s q) hq,mul_zero])

theorem ProductSolutionOn.const_mul
    {V : Set ((X n) × (X n))} (hV : IsOpen V) {g₁ g₂ : (MetricField n)}
    {F : (X n) × (X n) → ℝ} (hF : ProductSolutionOn g₁ g₂ V F) (a : ℝ) :
    ProductSolutionOn g₁ g₂ V (fun q => a * F q) := by
  refine ⟨contDiffOn_const.mul hF.1,?_,?_⟩
  · intro q hq
    let U := (fun x : (X n) => (x,q.2)) ⁻¹' V
    have hU : IsOpen U := hV.preimage (continuous_id.prodMk continuous_const)
    have hf : ContDiffOn ℝ ∞ (fun x => F (x,q.2)) U :=
      hF.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ h => h)
    exact (laplace_const_mul hU hf hq g₁ a).trans (by rw [hF.2.1 q hq,mul_zero])
  · intro q hq
    let U := (fun y : (X n) => (q.1,y)) ⁻¹' V
    have hU : IsOpen U := hV.preimage (continuous_const.prodMk continuous_id)
    have hf : ContDiffOn ℝ ∞ (fun y => F (q.1,y)) U :=
      hF.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
    exact (laplace_const_mul hU hf hq g₂ a).trans (by rw [hF.2.2 q hq,mul_zero])

theorem GreenGerm.productSolution
    {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n} (hg : SmoothMetric Ω g)
    {G : X n × X n → ℝ} (hG : GreenGerm Ω g G) :
    ProductSolutionOn g g (OffDiagonal Ω) G := by
  refine ⟨hG.1,?_,?_⟩
  · exact fun q hq => (hG.harmonic_left hΩ hg hq.2.1).2 q.1 ⟨hq.1,hq.2.2⟩
  · exact fun q hq => (hG.harmonic_right hΩ hg hq.1).2 q.2 ⟨hq.2.1,hq.2.2.symm⟩

/-- The equal-center specialization of the two-variable affine pullback. -/
theorem ProductSolutionOn.affineChart_pullback
    {V : Set (X n × X n)} (hV : IsOpen V) {g₁ g₂ : MetricField n}
    (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {F : X n × X n → ℝ} (hF : ProductSolutionOn g₁ g₂ V F) (c : X n) (s : ℝ) :
    ProductSolutionOn (affineChartMetric g₁ (c,s)) (affineChartMetric g₂ (c,s))
      (affineChartProduct c s ⁻¹' V) (F ∘ affineChartProduct c s) :=
  hF.separateAffineChart_pullback hV hg₁ hg₂ c c s

theorem ProductSolutionOn.affineChart_pushforward
    {V : Set ((X n) × (X n))} (hV : IsOpen V) {g₁ g₂ : (MetricField n)}
    (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {F : (X n) × (X n) → ℝ} {c : (X n)} {s : ℝ} (hs : s ≠ 0)
    (hF : ProductSolutionOn (affineChartMetric g₁ (c,s)) (affineChartMetric g₂ (c,s)) V F) :
    ProductSolutionOn g₁ g₂ (affineChartProduct c s '' V)
      (F ∘ affineChartProduct (-(s⁻¹ • c)) s⁻¹) := by
  have h := hF.affineChart_pullback hV (smoothMetric_affineChartMetric hg₁ (c,s))
    (smoothMetric_affineChartMetric hg₂ (c,s)) (-(s⁻¹ • c)) s⁻¹
  have he (g : (MetricField n)) :
      affineChartMetric (affineChartMetric g (c,s)) (-(s⁻¹ • c), s⁻¹) = g := by
    funext x
    exact congrArg g (affineChartMap_inverse_right c hs x)
  rw [he,he] at h
  refine h.mono ?_
  rintro _ ⟨x,hx,rfl⟩
  change affineChartProduct (-(s⁻¹ • c)) s⁻¹ (affineChartProduct c s x) ∈ V
  rwa [affineChartProduct_inverse c hs]

theorem isOpen_affineChartProduct_image (c : (X n)) {s : ℝ} (hs : s ≠ 0)
    {V : Set ((X n) × (X n))} (hV : IsOpen V) : IsOpen (affineChartProduct c s '' V) := by
  have he : affineChartProduct c s '' V =
      affineChartProduct (-(s⁻¹ • c)) s⁻¹ ⁻¹' V := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      simpa only [mem_preimage,affineChartProduct_inverse c hs] using hz
    · intro hx
      exact ⟨_,hx,affineChartProduct_inverse_right c hs x⟩
  rw [he]
  exact hV.preimage (contDiff_affineChartProduct _ _).continuous

end CalderonN
