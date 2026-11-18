import Proof.CovariantRotationGraphOperations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual second covariant product rule for one scalar weight and
one coarse operator family. Frame-connection terms are retained in the
genuine graphs used by both product rules. -/
lemma coarse_covariant_second_weighted_graph
    {d : Data} {y b c : X}
    (w : X → ℝ) (F S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Sc T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hw : ContDiffAt ℝ ∞ w y) (hF : DifferentiableAt ℝ F y)
    (hS : DifferentiableAt ℝ S y)
    (hFc : CoarseCovariantRotationGraph d y c F Sc)
    (hSc : CoarseCovariantRotationGraph d y c S T) :
    CoarseCovariantRotationGraph d y c
      (fun x => w x • S x+fderiv ℝ w x b • F x)
      ((w y • T+fderiv ℝ w y c • S y)+
        (fderiv ℝ w y b • Sc+fderiv ℝ (fun x => fderiv ℝ w x b) y c • F y)) := by
  have hwd : DifferentiableAt ℝ w y := hw.differentiableAt (by simp)
  have hwb : DifferentiableAt ℝ (fun x => fderiv ℝ w x b) y :=
    ((hw.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
  exact (hSc.smul w hwd hS).add
    (hFc.smul (fun x => fderiv ℝ w x b) hwb hF)
    (hwd.smul hS) (hwb.smul hF)

/-- Weighted second covariant graphs preserve the r beta squared gain.
This norm estimate concerns the same four product-rule coefficients. -/
lemma norm_coarse_second_weighted_jet_le
    (F Sb Sc T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (w wb wc wbc B C0 C1 C2 r β : ℝ)
    (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hw : |w| ≤ B) (hwb : |wb| ≤ B*β) (hwc : |wc| ≤ B*β) (hwbc : |wbc| ≤ B*β^2)
    (hF : ‖F‖ ≤ C0*r) (hSb : ‖Sb‖ ≤ C1*r*β) (hSc : ‖Sc‖ ≤ C1*r*β)
    (hT : ‖T‖ ≤ C2*r*β^2) :
    ‖(w • T+wc • Sb)+(wb • Sc+wbc • F)‖ ≤ B*(C2+2*C1+C0)*r*β^2 := by
  have h0 : ‖w • T‖ ≤ B*(C2*r*β^2) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hw hT (norm_nonneg _) hB
  have h1 : ‖wc • Sb‖ ≤ (B*β)*(C1*r*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwc hSb (norm_nonneg _) (mul_nonneg hB hβ)
  have h2 : ‖wb • Sc‖ ≤ (B*β)*(C1*r*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwb hSc (norm_nonneg _) (mul_nonneg hB hβ)
  have h3 : ‖wbc • F‖ ≤ (B*β^2)*(C0*r) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwbc hF (norm_nonneg _) (mul_nonneg hB (sq_nonneg _))
  calc
    _ ≤ (‖w • T‖+‖wc • Sb‖)+(‖wb • Sc‖+‖wbc • F‖) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ (B*(C2*r*β^2)+(B*β)*(C1*r*β))+((B*β)*(C1*r*β)+(B*β^2)*(C0*r)) :=
      add_le_add (add_le_add h0 h1) (add_le_add h2 h3)
    _ = _ := by ring

end ShrinkingSpheres
