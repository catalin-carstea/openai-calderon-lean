module

public import Proof.CalderonN.InteriorJetCutoff
public import Proof.CalderonN.ClassicalInteriorJets
import Proof.CalderonN.CrossTensor
public import Proof.CalderonN.StrongCrossExtension

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

public section

set_option maxHeartbeats 1800000

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open LocalMetricExtension (integral_sq_eq_norm_sq)

private theorem slicePointwise_of_jet (U : Set (X dim)) (H : Set (X dim)) (C : ℝ)
    (g : (MetricField dim))
    (hjet : ∀ (u : ChartL2 (d := dim) U) (f : (X dim) → ℝ), Harmonic U g f →
      (u : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict U] f →
        ∀ x ∈ H, ‖iteratedFDeriv ℝ 0 f x‖ ≤ C * ‖u‖)
    {f : (X dim) → ℝ} (hf : Harmonic U g f)
    (hi : IntegrableOn (fun x => (f x)^2) U)
    (hm : AEStronglyMeasurable f ((volume : Measure (X dim)).restrict U)) {x : (X dim)} (hx : x ∈ H) :
    (f x)^2 ≤ C^2 * ∫ z in U, (f z)^2 := by
  have hLp := (memLp_two_iff_integrable_sq hm).mpr hi
  let u := hLp.toLp f
  have hu : (u : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict U] f := MemLp.coeFn_toLp hLp
  have h := hjet u f hf hu x hx
  have hzero : ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖ := norm_iteratedFDeriv_zero
  rw [hzero] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hInt : ∫ z in U, (f z)^2 = ‖u‖^2 :=
    (integral_congr_ae (hu.mono (fun z hz => congrArg (fun b : ℝ => b^2) hz.symm))).trans
      (integral_sq_eq_norm_sq u)
  rw [Real.norm_eq_abs,sq_abs,mul_pow,← hInt] at hs
  exact hs

/-- Product-harmonic continuations have a uniform pointwise estimate on
compact rectangles from the L² norm of their output on an open rectangle. -/
theorem exists_uniform_product_harmonic_pointwise_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {J : Set P} (hJ : IsCompact J)
    {D₁ D₂ K₁ K₂ : Set (X dim)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hK₁D₁ : K₁ ⊆ D₁) (hK₂D₂ : K₂ ⊆ D₂)
    {g₁ g₂ : P → (MetricField dim)}
    (hg₁ : ∀ p ∈ J, SmoothMetric D₁ (g₁ p))
    (hg₂ : ∀ p ∈ J, SmoothMetric D₂ (g₂ p))
    (ha₁ : ∀ i j, ContDiffOn ℝ ∞
      (fun q : P × (X dim) => divergenceCoeff (g₁ q.1) q.2 i j) ((univ : Set P) ×ˢ D₁))
    (ha₂ : ∀ i j, ContDiffOn ℝ ∞
      (fun q : P × (X dim) => divergenceCoeff (g₂ q.1) q.2 i j) ((univ : Set P) ×ˢ D₂)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ (Q : ChartProductL2 (d := dim) D₁ D₂) (F : (X dim) × (X dim) → ℝ),
      ProductSolutionOn (g₁ p) (g₂ p) (D₁ ×ˢ D₂) F →
      (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict D₁).prod ((volume : Measure (X dim)).restrict D₂)] F →
      ∀ q ∈ K₁ ×ˢ K₂, |F q| ≤ C * ‖Q‖ := by
  obtain ⟨U₁,hU₁,hK₁U₁,hU₁D₁,hU₁c⟩ := exists_open_between_and_isCompact_closure hK₁ hD₁ hK₁D₁
  obtain ⟨U₂,hU₂,hK₂U₂,hU₂D₂,hU₂c⟩ := exists_open_between_and_isCompact_closure hK₂ hD₂ hK₂D₂
  have h₁ : U₁ ⊆ D₁ := subset_closure.trans hU₁D₁
  have h₂ : U₂ ⊆ D₂ := subset_closure.trans hU₂D₂
  obtain ⟨C₁,hC₁,h₁jet⟩ := exists_uniform_harmonic_interior_jet_bound hJ hU₁
    (fun p hp => smoothMetric_restrict (hg₁ p hp) h₁)
    (fun i j => (ha₁ i j).mono (prod_mono Subset.rfl h₁)) hK₁ hK₁U₁ 0
  obtain ⟨C₂,hC₂,h₂jet⟩ := exists_uniform_harmonic_interior_jet_bound hJ hU₂
    (fun p hp => smoothMetric_restrict (hg₂ p hp) h₂)
    (fun i j => (ha₂ i j).mono (prod_mono Subset.rfl h₂)) hK₂ hK₂U₂ 0
  refine ⟨C₁*C₂,mul_nonneg hC₁ hC₂,?_⟩
  intro p hp Q F hF hRep q hq
  let μ₁ := (volume : Measure (X dim)).restrict U₁
  let μ₂ := (volume : Measure (X dim)).restrict U₂
  let ν := ((volume : Measure (X dim)).restrict D₁).prod ((volume : Measure (X dim)).restrict D₂)
  have hν : μ₁.prod μ₂ ≤ ν :=
    Measure.prod_mono (Measure.restrict_mono_set _ h₁) (Measure.restrict_mono_set _ h₂)
  have hνi : Integrable (fun z => (F z)^2) ν :=
    (Lp.memLp Q).integrable_sq.congr (hRep.mono fun z hz => congrArg (fun b : ℝ => b^2) hz)
  have hμi : Integrable (fun z => (F z)^2) (μ₁.prod μ₂) := hνi.mono_measure hν
  have hL2 : ∫ z, (F z)^2 ∂μ₁.prod μ₂ ≤ ‖Q‖^2 := by
    calc
      _ ≤ ∫ z, (F z)^2 ∂ν := integral_mono_measure hν (ae_of_all _ (fun _ => sq_nonneg _)) hνi
      _ = ∫ z, (Q z)^2 ∂ν := integral_congr_ae (hRep.mono (fun z hz => congrArg (fun b : ℝ => b^2) hz.symm))
      _ = _ := integral_sq_eq_norm_sq Q
  have hy : q.2 ∈ D₂ := hK₂D₂ hq.2
  have hLeft : Harmonic U₁ (g₁ p) (fun x => F (x,q.2)) :=
    ⟨hF.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => ⟨h₁ hx,hy⟩),
      fun x hx => hF.2.1 (x,q.2) ⟨h₁ hx,hy⟩⟩
  have hLc : ContinuousOn (fun x => F (x,q.2)) (closure U₁) :=
    hF.1.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hx => ⟨hU₁D₁ hx,hy⟩)
  have hLint : Integrable (fun x => (F (x,q.2))^2) μ₁ :=
    ((hLc.pow 2).integrableOn_compact hU₁c).mono_set subset_closure
  have hAt := slicePointwise_of_jet U₁ K₁ C₁ (g₁ p) (h₁jet p hp) hLeft hLint
    (hLeft.1.continuousOn.aestronglyMeasurable hU₁.measurableSet) hq.1
  have hNext (z : (X dim)) (hz : z ∈ U₁) :
      (F (z,q.2))^2 ≤ C₂^2 * ∫ y, (F (z,y))^2 ∂μ₂ := by
    have hR : Harmonic U₂ (g₂ p) (fun y => F (z,y)) :=
      ⟨hF.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => ⟨h₁ hz,h₂ hy⟩),
        fun y hy => hF.2.2 (z,y) ⟨h₁ hz,h₂ hy⟩⟩
    have hRc : ContinuousOn (fun y => F (z,y)) (closure U₂) :=
      hF.1.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hy => ⟨h₁ hz,hU₂D₂ hy⟩)
    have hRi : Integrable (fun y => (F (z,y))^2) μ₂ :=
      ((hRc.pow 2).integrableOn_compact hU₂c).mono_set subset_closure
    exact slicePointwise_of_jet U₂ K₂ C₂ (g₂ p) (h₂jet p hp) hR hRi
      (hR.1.continuousOn.aestronglyMeasurable hU₂.measurableSet) hq.2
  have hμ₁ : (∫ z, (F (z,q.2))^2 ∂μ₁) ≤ C₂^2 * ‖Q‖^2 := by
    calc
      _ ≤ ∫ z, C₂^2 * ∫ y, (F (z,y))^2 ∂μ₂ ∂μ₁ :=
        integral_mono_ae hLint (hμi.integral_prod_left.const_mul _)
          (ae_restrict_of_forall_mem hU₁.measurableSet hNext)
      _ = C₂^2 * ∫ z, (F z)^2 ∂μ₁.prod μ₂ := by
        rw [integral_const_mul,integral_prod _ hμi]
      _ ≤ _ := mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)
  apply abs_le_of_sq_le_sq _ (mul_nonneg (mul_nonneg hC₁ hC₂) (norm_nonneg _))
  calc
    _ ≤ C₁^2 * ∫ z, (F (z,q.2))^2 ∂μ₁ := hAt
    _ ≤ C₁^2 * (C₂^2 * ‖Q‖^2) := mul_le_mul_of_nonneg_left hμ₁ (sq_nonneg _)
    _ = _ := by ring

end CalderonN
