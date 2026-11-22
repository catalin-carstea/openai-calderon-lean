module

public import Proof.Manuscript.ScalarProductGluing
public import Proof.CalderonN.CompactProductCross

import Proof.CalderonN.CrossTensor
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ENNReal

namespace CalderonPaper.ScalarElliptic

private theorem lpNorm_l2_le_measure_of_ae_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂μ, |f x| ≤ M) :
    lpNorm f 2 μ ≤ Real.sqrt (μ.real univ) * M := by
  let u := hf.toLp f
  have hnorm : ‖u‖ = lpNorm f 2 μ := Lp.norm_toLp _ _
  have hu : (∫ x, f x^2 ∂μ) = ‖u‖^2 := by
    rw [← integral_sq_eq_norm_sq u]
    exact integral_congr_ae (hf.coeFn_toLp.symm.mono fun _ hx => congrArg (fun r : ℝ => r^2) hx)
  have hP := integral_mono_ae hf.integrable_sq (integrable_const (M^2))
    (hbound.mono fun x hx => (sq_abs (f x)).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) hx 2))
  rw [integral_const,smul_eq_mul,hu,hnorm] at hP
  apply (sq_le_sq₀ (lpNorm_nonneg ..) (mul_nonneg (Real.sqrt_nonneg _) hM)).mp
  rwa [mul_pow,Real.sq_sqrt measureReal_nonneg]

variable {n : ℕ} [NeZero n]

private theorem cross_bound {A B : Set (X n)} (hA : IsOpen A) (hB : IsOpen B)
    (hAc : IsCompact (closure A)) (hBc : IsCompact (closure B))
    {F : X n × X n → ℝ} (hF : ContinuousOn F (closure A ×ˢ closure B))
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ z ∈ closure A ×ˢ closure B, |F z| ≤ M) :
    MemLp F 2 (crossMeasure A B) ∧
      lpNorm F 2 (crossMeasure A B) ≤ Real.sqrt ((crossMeasure A B).real univ) * M := by
  let : IsFiniteMeasure ((volume : Measure (X n)).restrict A) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt hAc.measure_lt_top).ne
  let : IsFiniteMeasure ((volume : Measure (X n)).restrict B) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt hBc.measure_lt_top).ne
  let : IsFiniteMeasure (crossMeasure A B) := by
    unfold crossMeasure
    infer_instance
  have hMem : MemLp F 2 (crossMeasure A B) := by
    unfold crossMeasure
    rw [Measure.prod_restrict]
    have hsub : A ×ˢ B ⊆ closure A ×ˢ closure B := Set.prod_mono subset_closure subset_closure
    have hmeas := (hF.mono hsub).aestronglyMeasurable (hA.prod hB).measurableSet
      (μ := (volume : Measure (X n)).prod volume)
    exact (memLp_two_iff_integrable_sq hmeas).mpr
      (((hF.pow 2).integrableOn_compact (hAc.prod hBc)).mono_set hsub)
  refine ⟨hMem,lpNorm_l2_le_measure_of_ae_bound hMem hM ?_⟩
  change ∀ᵐ z ∂((volume : Measure (X n)).restrict A).prod (volume.restrict B), |F z| ≤ M
  rw [Measure.prod_restrict]
  exact (ae_restrict_mem (hA.prod hB).measurableSet).mono (fun z hz =>
    hbound z (Set.prod_mono subset_closure subset_closure hz))

/-- Supremum control on the two compact input arms gives the actual
cross's sum of chart L² norms. The conversion cost is fixed by the arms. -/
theorem exists_scalar_crossData_of_compact_arms {D₁ D₂ S₁ S₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂)
    (hcD₁ : IsCompact (closure D₁)) (hcD₂ : IsCompact (closure D₂))
    (hcS₁ : IsCompact (closure S₁)) (hcS₂ : IsCompact (closure S₂)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U : Set (X n × X n)},
      ((closure D₁ ×ˢ closure S₂) ∪ (closure S₁ ×ˢ closure D₂)) ⊆ U →
      ∀ {L₁ L₂ : ScalarElliptic n} {F : X n × X n → ℝ}, L₁.ProductSolvesOn L₂ U F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ (closure D₁ ×ˢ closure S₂) ∪ (closure S₁ ×ˢ closure D₂), |F z| ≤ M) →
      CrossData L₁ L₂ D₁ D₂ S₁ S₂ F (C*M) := by
  let C₁ := Real.sqrt ((crossMeasure D₁ S₂).real univ)
  let C₂ := Real.sqrt ((crossMeasure S₁ D₂).real univ)
  refine ⟨C₁+C₂,add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),?_⟩
  intro U hKU L₁ L₂ F hF M hM hbound
  have h₁ : closure D₁ ×ˢ closure S₂ ⊆ U := subset_union_left.trans hKU
  have h₂ : closure S₁ ×ˢ closure D₂ ⊆ U := subset_union_right.trans hKU
  obtain ⟨hMem₁,hn₁⟩ := cross_bound hD₁ hS₂ hcD₁ hcS₂ (hF.1.continuousOn.mono h₁)
    hM (fun z hz => hbound z (Or.inl hz))
  obtain ⟨hMem₂,hn₂⟩ := cross_bound hS₁ hD₂ hcS₁ hcD₂ (hF.1.continuousOn.mono h₂)
    hM (fun z hz => hbound z (Or.inr hz))
  exact ⟨hF.mono ((Set.prod_mono subset_closure subset_closure).trans h₁),
    hF.mono ((Set.prod_mono subset_closure subset_closure).trans h₂),hMem₁,hMem₂,
    (add_le_add hn₁ hn₂).trans_eq (by dsimp [C₁,C₂]; ring)⟩

end CalderonPaper.ScalarElliptic
