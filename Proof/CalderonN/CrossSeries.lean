module

public import Proof.CalderonN.CrossArmCoefficients
public import Proof.CalderonN.CrossWeakCoefficients

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace CalderonN

variable {d : ℕ} [NeZero d]
open LocalMetricExtension

private abbrev chartMeasure (D : Set (X d)) : Measure (X d) := (volume : Measure (X d)).restrict D

abbrev ChartProductL2 (D₁ D₂ : Set (X d)) := Lp ℝ 2
  (((volume : Measure (X d)).restrict D₁).prod ((volume : Measure (X d)).restrict D₂))

/-- The coefficient inequalities used on a single variable of the cross. -/
@[expose] def HarmonicInterpolation {D : Set (X d)} (hD : IsOpen D) {g : (MetricField d)} (hg : SmoothMetric D g)
    {S O : Set (X d)} (hSD : S ⊆ D) (hOD : O ⊆ D) (C γ : ℝ) : Prop :=
  ∀ u : harmonicL2Space hD hg, ‖harmonicRestrict hD hg hOD u‖ ≤
    C * ‖harmonicRestrict hD hg hSD u‖ ^ γ * ‖u‖ ^ (1 - γ)

theorem ae_firstArm_slices {D S : Set (X d)} (hD : IsOpen D) (hS : MeasurableSet S)
    {g : (MetricField d)} (hg : SmoothMetric D g) {q : ChartProductL2 (d := d) D S} {F : (X d) × (X d) → ℝ}
    (hq : (q : (X d) × (X d) → ℝ) =ᵐ[((volume : Measure (X d)).restrict D).prod
      ((volume : Measure (X d)).restrict S)] F)
    (hF : ∀ y ∈ S, Harmonic D g (fun x => F (x,y))) :
    ∀ᵐ y ∂(volume : Measure (X d)).restrict S, ∃ u : harmonicL2Space hD hg,
      (u.1 : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict D] fun x => q (x,y) := by
  have h' := (Measure.measurePreserving_swap
    (μ := chartMeasure S) (ν := chartMeasure D)).quasiMeasurePreserving.ae hq
  filter_upwards [Measure.ae_ae_of_ae_prod h', ae_memLp_left_of_prod q,
    ae_restrict_mem hS] with y hy hL hyS
  have hy' : (fun x => q (x,y)) =ᵐ[chartMeasure D] fun x => F (x,y) := hy
  have hMem := hL.ae_eq hy'
  exact ⟨⟨hMem.toLp _, harmonic_mem_harmonicL2Space hD hg (hF y hyS) hMem⟩,
    hMem.coeFn_toLp.trans hy'.symm⟩

private theorem norm_restrict_basis {D S : Set (X d)} (hD : IsOpen D) {g : (MetricField d)}
    (hg : SmoothMetric D g) (hSD : S ⊆ D)
    {ι : Type*} [DecidableEq ι] (w : HilbertBasis ι ℝ (harmonicL2Space hD hg))
    (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (harmonicRestrict hD hg hSD (w i))
      (harmonicRestrict hD hg hSD (w j)) = if i = j then μ i ^ 2 else 0) :
    ∀ i, ‖harmonicRestrict hD hg hSD (w i)‖ = μ i := by
  intro i
  apply (sq_eq_sq₀ (norm_nonneg _) (hμ i).le).mp
  simpa [real_inner_self_eq_norm_sq] using hgram i i

/-- The series with the manuscript's actual coefficients converges in the
output product and has the claimed linear norm bound. The two interpolation
inequalities and the spectral majorant enter at their original points. -/
theorem exists_crossSeries_L2
    {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X d)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hS₁D₁ : S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂) (hO₁D₁ : O₁ ⊆ D₁) (hO₂D₂ : O₂ ⊆ D₂)
    {g₁ g₂ : (MetricField d)} (hg₁ : SmoothMetric D₁ g₁) (hg₂ : SmoothMetric D₂ g₂)
    (hfinite : (volume : Measure (X d)) D₂ ≠ ⊤)
    (q₁ : ChartProductL2 (d := d) D₁ S₂) (q₂ : ChartProductL2 (d := d) S₁ D₂) {F : (X d) × (X d) → ℝ}
    (hq₁ : (q₁ : (X d) × (X d) → ℝ) =ᵐ[((volume : Measure (X d)).restrict D₁).prod
      ((volume : Measure (X d)).restrict S₂)] F)
    (hq₂ : (q₂ : (X d) × (X d) → ℝ) =ᵐ[((volume : Measure (X d)).restrict S₁).prod
      ((volume : Measure (X d)).restrict D₂)] F)
    (hF₁ : ∀ y ∈ S₂, Harmonic D₁ g₁ (fun x => F (x,y)))
    (hF₂ : ∀ x ∈ S₁, Harmonic D₂ g₂ (fun y => F (x,y)))
    {ι : Type*} [DecidableEq ι] (w : HilbertBasis ι ℝ (harmonicL2Space hD₁ hg₁))
    (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i, ((harmonicRestrict hD₁ hg₁ hS₁D₁).adjoint ∘L
      harmonicRestrict hD₁ hg₁ hS₁D₁) (w i) = μ i ^ 2 • w i)
    (hgram : ∀ i j, inner ℝ (harmonicRestrict hD₁ hg₁ hS₁D₁ (w i))
      (harmonicRestrict hD₁ hg₁ hS₁D₁ (w j)) = if i = j then μ i ^ 2 else 0)
    {C₁ C₂ γ₁ γ₂ M P : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM : 0 ≤ M)
    (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1)
    (hfirst : HarmonicInterpolation hD₁ hg₁ hS₁D₁ hO₁D₁ C₁ γ₁)
    (hsecond : HarmonicInterpolation hD₂ hg₂ hS₂D₂ hO₂D₂ C₂ γ₂)
    (hM₁ : ‖q₁‖ ≤ M) (hM₂ : ‖q₂‖ ≤ M)
    (hsum : Summable fun i => μ i ^ (γ₁ + γ₂ - 1))
    (hP : (∑' i, μ i ^ (γ₁ + γ₂ - 1)) ≤ P) :
    ∃ b : ι → harmonicL2Space hD₂ hg₂, ∃ Q : ChartProductL2 O₁ O₂,
      (∀ i, (b i).1 = crossArmCoefficient (harmonicRestrict hD₁ hg₁ hS₁D₁ (w i)) (μ i) q₂) ∧
      (∀ i, harmonicRestrict hD₂ hg₂ hS₂D₂ (b i) =
        tensorCoefficient (w i).1 q₁) ∧
      (Summable fun i => ‖tensorLp (harmonicRestrict hD₁ hg₁ hO₁D₁ (w i))
        (harmonicRestrict hD₂ hg₂ hO₂D₂ (b i))‖) ∧
      HasSum (fun i => tensorLp (harmonicRestrict hD₁ hg₁ hO₁D₁ (w i))
        (harmonicRestrict hD₂ hg₂ hO₂D₂ (b i))) Q ∧
      ‖Q‖ ≤ C₁ * C₂ * M * P := by
  let R := harmonicRestrict hD₁ hg₁ hS₁D₁
  let J := (harmonicL2Space hD₁ hg₁).toSubmodule.subtypeₗᵢ
  let hm := Measure.restrict_mono_set (volume : Measure (X d)) hS₁D₁
  let hn := Measure.restrict_mono_set (volume : Measure (X d)) hS₂D₂
  let : IsFiniteMeasure (chartMeasure D₂) := isFiniteMeasure_restrict.mpr hfinite
  let : IsFiniteMeasure (chartMeasure S₂) :=
    ⟨(measure_mono (μ := chartMeasure S₂) (subset_univ _)).trans_lt
      (lt_of_le_of_lt (hn Set.univ) (measure_lt_top (chartMeasure D₂) Set.univ))⟩
  have hagree : (q₁ : (X d) × (X d) → ℝ) =ᵐ[(chartMeasure S₁).prod (chartMeasure S₂)] q₂ :=
    Filter.EventuallyEq.trans (ae_mono (Measure.prod_mono hm le_rfl) hq₁)
      (Filter.EventuallyEq.symm (ae_mono (Measure.prod_mono le_rfl hn) hq₂))
  have hbweak (i : ι) : crossArmCoefficient (R (w i)) (μ i) q₂ ∈ harmonicL2Space hD₂ hg₂ := by
    rw [crossArmCoefficient]
    exact (harmonicL2Space hD₂ hg₂).smul_mem ((μ i) ^ 2)⁻¹
      (tensorCoefficient_mem_harmonicL2Space hS₁ hD₂ hg₂ (R (w i)) q₂ hq₂ hF₂)
  let b (i : ι) : harmonicL2Space hD₂ hg₂ := ⟨_, hbweak i⟩
  have hRnorm : ∀ i, ‖harmonicRestrict hD₁ hg₁ hS₁D₁ (w i)‖ = μ i :=
    norm_restrict_basis hD₁ hg₁ hS₁D₁ w μ hμ hgram
  have hfc (i : ι) : ‖harmonicRestrict hD₁ hg₁ hO₁D₁ (w i)‖ ≤ C₁ * μ i ^ γ₁ := by
    simpa only [hRnorm i, w.orthonormal.1 i, Real.one_rpow, mul_one] using hfirst (w i)
  have hbD₂ (i : ι) : ‖b i‖ ≤ (μ i)⁻¹ * M :=
    (norm_crossArmCoefficient_le (hμ i) (hRnorm i) q₂).trans
      (mul_le_mul_of_nonneg_left hM₂ (inv_nonneg.mpr (hμ i).le))
  have heq (i : ι) : harmonicRestrict hD₂ hg₂ hS₂D₂ (b i) = tensorCoefficient (w i).1 q₁ := by
    have hR (u : harmonicL2Space hD₁ hg₁) : R u = restrictL2 hm (J u) :=
      Lp.ext ((harmonicRestrict_ae hD₁ hg₁ hS₁D₁ u).trans (restrictL2_ae hm (J u)).symm)
    have hrb : harmonicRestrict hD₂ hg₂ hS₂D₂ (b i) =
        restrictL2 hn (crossArmCoefficient (R (w i)) (μ i) q₂) :=
      Lp.ext ((harmonicRestrict_ae hD₂ hg₂ hS₂D₂ (b i)).trans (restrictL2_ae hn (b i).1).symm)
    rw [hrb, crossArmCoefficient_restrict_eq w μ R J hm hn hR hμ heigen q₁ q₂
      hagree (ae_firstArm_slices hD₁ hS₂ hg₁ hq₁ hF₁) i]
    rfl
  have hbS₂ (i : ι) : ‖harmonicRestrict hD₂ hg₂ hS₂D₂ (b i)‖ ≤ M := by
    rw [heq]
    exact (norm_tensorCoefficient_le (J (w i)) q₁).trans (by
      rw [J.norm_map, w.orthonormal.1 i, one_mul]; exact hM₁)
  have hbc (i : ι) :
      ‖harmonicRestrict hD₂ hg₂ hO₂D₂ (b i)‖ ≤ (C₂ * M) * μ i ^ (γ₂ - 1) := by
    calc
      _ ≤ C₂ * M ^ γ₂ * ((μ i)⁻¹ * M) ^ (1 - γ₂) := (hsecond (b i)).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hbS₂ i) hγ₂.le) hC₂)
          (Real.rpow_le_rpow (norm_nonneg _) (hbD₂ i) (sub_nonneg.mpr hγ₂'))
          (Real.rpow_nonneg (norm_nonneg _) _) (mul_nonneg hC₂ (Real.rpow_nonneg hM _)))
      _ = _ := by
        rw [Real.mul_rpow (inv_nonneg.mpr (hμ i).le) hM, ← Real.rpow_neg_eq_inv_rpow,
          show -(1 - γ₂) = γ₂ - 1 by ring]
        by_cases h : M = 0
        · subst M
          rw [Real.zero_rpow hγ₂.ne']
          simp
        · have hsumM : M ^ γ₂ * M ^ (1 - γ₂) = M := by
            rw [← Real.rpow_add (lt_of_le_of_ne hM (Ne.symm h)), add_sub_cancel, Real.rpow_one]
          calc
            _ = C₂ * (M ^ γ₂ * M ^ (1 - γ₂)) * μ i ^ (γ₂ - 1) := by ring
            _ = _ := by rw [hsumM]
  let f (i : ι) := harmonicRestrict hD₁ hg₁ hO₁D₁ (w i)
  let c (i : ι) := harmonicRestrict hD₂ hg₂ hO₂D₂ (b i)
  have habs := tensor_norm_summable_of_rpow_bounds f c μ hμ C₁ (C₂ * M) γ₁ γ₂ hC₁ hfc hbc hsum
  refine ⟨b, ∑' i, tensorLp (f i) (c i), fun _ => rfl, heq, habs, habs.of_norm.hasSum, ?_⟩
  exact (norm_tsum_tensorLp_le_power_sum f c μ hμ C₁ (C₂ * M) γ₁ γ₂ hC₁ hfc hbc hsum).trans
    ((mul_le_mul_of_nonneg_left hP (by positivity)).trans_eq (by ring))

end CalderonN
