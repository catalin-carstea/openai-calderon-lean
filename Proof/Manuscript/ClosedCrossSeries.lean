module

public import Proof.CalderonN.CrossSeries

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

public section

open Set Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ENNReal

noncomputable section

namespace CalderonPaper

variable {d : ℕ}

abbrev chartMeasure (D : Set (X d)) : Measure (X d) := volume.restrict D

/-- Restriction of a member of a closed coordinate L² subspace. -/
@[expose] def closedRestrict {D S : Set (X d)} (H : ClosedSubmodule ℝ (ChartL2 D))
    (hSD : S ⊆ D) : H →L[ℝ] ChartL2 S :=
  (restrictL2 (Measure.restrict_mono_set volume hSD)).comp H.toSubmodule.subtypeL

@[expose] def ClosedInterpolation {D S O : Set (X d)}
    (H : ClosedSubmodule ℝ (ChartL2 D)) (hSD : S ⊆ D) (hOD : O ⊆ D) (C γ : ℝ) : Prop :=
  ∀ u : H, ‖closedRestrict H hOD u‖ ≤
    C * ‖closedRestrict H hSD u‖ ^ γ * ‖u‖ ^ (1 - γ)

/-- Fubini and orthogonality transfer pointwise-in-the-first-variable
closed-subspace membership to the second-variable tensor coefficient.
This is the Hilbert argument of the released `CrossWeakCoefficients`
with its harmonic-specific slice producer factored out. -/
theorem tensorCoefficient_mem_of_slices {S U : Set (X d)}
    (H : ClosedSubmodule ℝ (ChartL2 U)) (v : ChartL2 S) (Q : ChartProductL2 S U)
    (hSlice : ∀ᵐ x ∂chartMeasure S, ∃ w : H, (w.1 : X d → ℝ) =ᵐ[chartMeasure U]
      (fun y => Q (x,y))) :
    tensorCoefficient v Q ∈ H := by
  rw [← ClosedSubmodule.orthogonal_orthogonal_eq H, ClosedSubmodule.mem_orthogonal']
  intro ψ hψ
  rw [tensorCoefficient_inner_integral]
  calc
    _ = ∫ x in S, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [hSlice] with x hx
      obtain ⟨w,hRep⟩ := hx
      have hz := (ClosedSubmodule.mem_orthogonal H ψ).mp hψ w.1 w.2
      have htest : (∫ y in U, Q (x,y) * ψ y) = inner ℝ w.1 ψ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hRep] with y hy
        rw [RCLike.inner_apply,conj_trivial,show w.1 y = Q (x,y) from hy]
        ring
      rw [htest,hz,mul_zero]
    _ = 0 := integral_zero _ _

private theorem norm_restrict_closedBasis {D S : Set (X d)}
    (H : ClosedSubmodule ℝ (ChartL2 D)) (hSD : S ⊆ D)
    {ι : Type*} [DecidableEq ι] (w : HilbertBasis ι ℝ H)
    (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (closedRestrict H hSD (w i))
      (closedRestrict H hSD (w j)) = if i = j then μ i ^ 2 else 0) :
    ∀ i, ‖closedRestrict H hSD (w i)‖ = μ i := by
  intro i
  apply (sq_eq_sq₀ (norm_nonneg _) (hμ i).le).mp
  simpa [real_inner_self_eq_norm_sq] using hgram i i

/-- Closed-space form of the series proof in the released
`Proof.CalderonN.CrossSeries`. The first-arm Gram identity and the
two interpolation estimates determine the same normalized coefficients. -/
theorem exists_closed_crossSeries
    {D₁ D₂ S₁ S₂ O₁ O₂ : Set (X d)}
    (hS₁D₁ : S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂) (hO₁D₁ : O₁ ⊆ D₁) (hO₂D₂ : O₂ ⊆ D₂)
    (H₁ : ClosedSubmodule ℝ (ChartL2 D₁)) (H₂ : ClosedSubmodule ℝ (ChartL2 D₂))
    (hfinite : (volume : Measure (X d)) D₂ ≠ ⊤)
    (q₁ : ChartProductL2 D₁ S₂) (q₂ : ChartProductL2 S₁ D₂)
    (hAgree : (q₁ : X d × X d → ℝ) =ᵐ[(chartMeasure S₁).prod (chartMeasure S₂)] q₂)
    (hSlice₁ : ∀ᵐ y ∂chartMeasure S₂, ∃ u : H₁, (u.1 : X d → ℝ) =ᵐ[chartMeasure D₁]
      (fun x => q₁ (x,y)))
    (hSlice₂ : ∀ᵐ x ∂chartMeasure S₁, ∃ u : H₂, (u.1 : X d → ℝ) =ᵐ[chartMeasure D₂]
      (fun y => q₂ (x,y)))
    {ι : Type*} [DecidableEq ι] (w : HilbertBasis ι ℝ H₁)
    (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (heigen : ∀ i, ((closedRestrict H₁ hS₁D₁).adjoint ∘L
      closedRestrict H₁ hS₁D₁) (w i) = μ i ^ 2 • w i)
    (hgram : ∀ i j, inner ℝ (closedRestrict H₁ hS₁D₁ (w i))
      (closedRestrict H₁ hS₁D₁ (w j)) = if i = j then μ i ^ 2 else 0)
    {C₁ C₂ γ₁ γ₂ M P : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM : 0 ≤ M)
    (hγ₂ : 0 < γ₂) (hγ₂' : γ₂ ≤ 1)
    (hfirst : ClosedInterpolation H₁ hS₁D₁ hO₁D₁ C₁ γ₁)
    (hsecond : ClosedInterpolation H₂ hS₂D₂ hO₂D₂ C₂ γ₂)
    (hM₁ : ‖q₁‖ ≤ M) (hM₂ : ‖q₂‖ ≤ M)
    (hsum : Summable fun i => μ i ^ (γ₁ + γ₂ - 1))
    (hP : (∑' i, μ i ^ (γ₁ + γ₂ - 1)) ≤ P) :
    ∃ b : ι → H₂, ∃ Q : ChartProductL2 O₁ O₂,
      (∀ i, (b i).1 = crossArmCoefficient (closedRestrict H₁ hS₁D₁ (w i)) (μ i) q₂) ∧
      (∀ i, closedRestrict H₂ hS₂D₂ (b i) = tensorCoefficient (w i).1 q₁) ∧
      (Summable fun i => ‖tensorLp (closedRestrict H₁ hO₁D₁ (w i))
        (closedRestrict H₂ hO₂D₂ (b i))‖) ∧
      HasSum (fun i => tensorLp (closedRestrict H₁ hO₁D₁ (w i))
        (closedRestrict H₂ hO₂D₂ (b i))) Q ∧
      (∑' i, ‖tensorLp (closedRestrict H₁ hO₁D₁ (w i))
        (closedRestrict H₂ hO₂D₂ (b i))‖) ≤ C₁ * C₂ * M * P := by
  let R := closedRestrict H₁ hS₁D₁
  let J := H₁.toSubmodule.subtypeₗᵢ
  let hm := Measure.restrict_mono_set (volume : Measure (X d)) hS₁D₁
  let hn := Measure.restrict_mono_set (volume : Measure (X d)) hS₂D₂
  let : IsFiniteMeasure (chartMeasure D₂) := isFiniteMeasure_restrict.mpr hfinite
  let : IsFiniteMeasure (chartMeasure S₂) :=
    ⟨(measure_mono (μ := chartMeasure S₂) (subset_univ _)).trans_lt
      (lt_of_le_of_lt (hn Set.univ) (measure_lt_top (chartMeasure D₂) Set.univ))⟩
  have hbweak (i : ι) : crossArmCoefficient (R (w i)) (μ i) q₂ ∈ H₂ := by
    rw [crossArmCoefficient]
    exact H₂.smul_mem ((μ i) ^ 2)⁻¹ (tensorCoefficient_mem_of_slices H₂ (R (w i)) q₂ hSlice₂)
  let b (i : ι) : H₂ := ⟨_, hbweak i⟩
  have hRnorm : ∀ i, ‖closedRestrict H₁ hS₁D₁ (w i)‖ = μ i :=
    norm_restrict_closedBasis H₁ hS₁D₁ w μ hμ hgram
  have hfc (i : ι) : ‖closedRestrict H₁ hO₁D₁ (w i)‖ ≤ C₁ * μ i ^ γ₁ := by
    simpa only [hRnorm i, w.orthonormal.1 i, Real.one_rpow, mul_one] using hfirst (w i)
  have hbD₂ (i : ι) : ‖b i‖ ≤ (μ i)⁻¹ * M :=
    (norm_crossArmCoefficient_le (hμ i) (hRnorm i) q₂).trans
      (mul_le_mul_of_nonneg_left hM₂ (inv_nonneg.mpr (hμ i).le))
  have heq (i : ι) : closedRestrict H₂ hS₂D₂ (b i) = tensorCoefficient (w i).1 q₁ := by
    exact crossArmCoefficient_restrict_eq w μ R J hm hn (fun _ => rfl) hμ heigen q₁ q₂
      hAgree hSlice₁ i
  have hbS₂ (i : ι) : ‖closedRestrict H₂ hS₂D₂ (b i)‖ ≤ M := by
    rw [heq]
    exact (norm_tensorCoefficient_le (J (w i)) q₁).trans (by
      rw [J.norm_map, w.orthonormal.1 i, one_mul]; exact hM₁)
  have hbc (i : ι) :
      ‖closedRestrict H₂ hO₂D₂ (b i)‖ ≤ (C₂ * M) * μ i ^ (γ₂ - 1) := by
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
  let f (i : ι) := closedRestrict H₁ hO₁D₁ (w i)
  let c (i : ι) := closedRestrict H₂ hO₂D₂ (b i)
  have habs := tensor_norm_summable_of_rpow_bounds f c μ hμ C₁ (C₂ * M) γ₁ γ₂ hC₁ hfc hbc hsum
  refine ⟨b, ∑' i, tensorLp (f i) (c i), fun _ => rfl, heq, habs, habs.of_norm.hasSum, ?_⟩
  have hterm (i : ι) : ‖tensorLp (f i) (c i)‖ ≤
      (C₁ * (C₂*M)) * μ i ^ (γ₁+γ₂-1) := by
    rw [norm_tensorLp, show γ₁+γ₂-1 = γ₁+(γ₂-1) by ring, Real.rpow_add (hμ i)]
    exact (mul_le_mul (hfc i) (hbc i) (norm_nonneg _) (mul_nonneg hC₁ (Real.rpow_nonneg (hμ i).le _))).trans_eq (by ring)
  calc
    _ ≤ ∑' i, (C₁ * (C₂*M)) * μ i ^ (γ₁+γ₂-1) :=
      habs.tsum_le_tsum hterm (hsum.mul_left _)
    _ = (C₁ * (C₂*M)) * ∑' i, μ i ^ (γ₁+γ₂-1) := tsum_mul_left
    _ ≤ _ := (mul_le_mul_of_nonneg_left hP (by positivity)).trans_eq (by ring)

end CalderonPaper
