module

public import Proof.CalderonN.ClassicalSourceEquation
public import Proof.CalderonN.SourceSobolev
import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.CompactSupport
import Mathlib.Tactic

public section

/-! Use a fixed interior cutoff to extend the classical representative.
The cutoff acts on the same weak solution and preserves its first-order
norm bound up to a fixed multiplicative constant. -/
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal Distributions Gradient Matrix.Norms.Elementwise

namespace CalderonN
open TauCeti
variable {n : ℕ}

set_option maxHeartbeats 3500000 in
theorem exists_cutoff_source_rep_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ w : FixedBallH1 n, ∀ b₀ : X n → ℝ,
      ContDiffOn ℝ ∞ b₀ (ball (0 : X n) (7/8)) →
      b₀ =ᵐ[volume.restrict (ball (0 : X n) (7/8))] ⇑(W1p.value w) →
      ∃ b : X n → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
        ⇑(W1p.value w) =ᵐ[volume.restrict (ball (0 : X n) (3/4))] b ∧
        (eLpNorm (fderiv ℝ b) 2 (volume.restrict (fixedBallOpens n))).toReal ≤ D * ‖w‖ ∧
        (eLpNorm b 2 (volume.restrict (fixedBallOpens n))).toReal ≤ D * ‖w‖ := by
  let ζ : ContDiffBump (0 : X n) := ⟨3/4, 13/16, by norm_num, by norm_num⟩
  let E := ball (0 : X n) (7/8)
  let V := fixedBallOpens n
  let μ := (volume : Measure (X n)).restrict V
  have hζE : tsupport ζ ⊆ E := by
    rw [ζ.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  have hEV : E ⊆ V := ball_subset_ball (by norm_num)
  have hVE : μ.restrict E = (volume : Measure (X n)).restrict E := by
    rw [Measure.restrict_restrict (isOpen_ball.measurableSet : MeasurableSet E),
      inter_eq_left.mpr hEV]
  have hζ₁ : ContDiff ℝ 1 (ζ : X n → ℝ) := ζ.contDiff
  obtain ⟨C,hC,hCζ,hCgrad⟩ := hζ₁.exists_abs_le_and_norm_gradient_le ζ.hasCompactSupport
  refine ⟨2*C+1, by positivity, fun w b₀ hb₀ hAE => ?_⟩
  let b := fun x => ζ x * b₀ x
  have hb : ContDiff ℝ ∞ b :=
    Elliptic.contDiff_mul_of_tsupport_subset (isOpen_ball : IsOpen E) ζ.contDiff hζE hb₀
  have hbK : HasCompactSupport b := ζ.hasCompactSupport.mul_right
  let w' := W1p.contDiffSMul (ζ : X n → ℝ) ζ.contDiff hC
    (fun x _ => hCζ x) (fun x _ => hCgrad x) w
  have hv := W1p.value_contDiffSMul_ae ζ.contDiff hC
    (fun x _ => hCζ x) (fun x _ => hCgrad x) w
  have hB : ⇑(W1p.value w') =ᵐ[μ] b := by
    have hA : ∀ᵐ x ∂μ, x ∈ E → b₀ x = W1p.value w x := by
      apply (ae_restrict_iff' (isOpen_ball.measurableSet : MeasurableSet E)).mp
      rw [hVE]
      exact hAE
    filter_upwards [hv,hA] with x hx hx'
    change W1p.value w' x = b x
    rw [show W1p.value w' x = ζ x * W1p.value w x from hx]
    by_cases h : x ∈ tsupport ζ
    · rw [← hx' (hζE h)]
    · simp only [b, image_eq_zero_of_notMem_tsupport h, zero_mul]
  have hInner : ⇑(W1p.value w) =ᵐ[volume.restrict (ball (0 : X n) (3/4))] b := by
    have hsub : ball (0 : X n) (3/4) ⊆ E := ball_subset_ball (by norm_num)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hAE,
      ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : X n) (3/4)))] with x hx hxB
    have hOne : ζ x = 1 := ζ.one_of_mem_closedBall (ball_subset_closedBall hxB)
    simp [b, hOne, hx]
  have hN : ‖w'‖ ≤ (2*C+1) * ‖w‖ := by
    refine (W1p.norm_contDiffSMul_le ζ.contDiff hC _ _ w).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hG : ⇑(W1p.gradient w') =ᵐ[μ] gradient b :=
    weak_gradient_eq_gradient_of_ae_value (U := V) le_rfl w' hb hB
  refine ⟨b,hb,hbK,hInner,?_,?_⟩
  · have hNormEq := eLpNorm_congr_norm_ae
      (μ := μ) (p := 2) (hb.continuous_fderiv (by simp)).aestronglyMeasurable
      (Lp.aestronglyMeasurable (W1p.gradient w'))
      (by
        filter_upwards [hG] with x hx
        rw [hx, norm_gradient_eq_norm_fderiv])
    rw [hNormEq, ← Lp.norm_def]
    exact (W1p.norm_gradient_le w').trans hN
  · rw [← eLpNorm_congr_ae hB, ← Lp.norm_def]
    exact (W1p.norm_value_le w').trans hN

end CalderonN
