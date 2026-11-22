module

public import Proof.CalderonN.CrossTensor

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Tactic.Ring

public section

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LocalMetricExtension

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {m : Measure α} {n : Measure β} [SFinite m] [SFinite n]

private def tensorRight (f : Lp ℝ 2 m) : Lp ℝ 2 n →L[ℝ] Lp ℝ 2 (m.prod n) := by
  let A : Lp ℝ 2 n →ₗ[ℝ] Lp ℝ 2 (m.prod n) :=
    { toFun := fun g => tensorLp f g
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [tensorLp_ae f (u + v), Lp.coeFn_add (tensorLp f u) (tensorLp f v),
          tensorLp_ae f u, tensorLp_ae f v, Measure.quasiMeasurePreserving_snd.ae
            (Lp.coeFn_add u v)] with z hz hsum hu hv hval
        simp only [hz, hsum, Pi.add_apply, hu, hv, hval]
        ring
      map_smul' := by
        intro c u
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [tensorLp_ae f (c • u), Lp.coeFn_smul c (tensorLp f u), tensorLp_ae f u,
          Measure.quasiMeasurePreserving_snd.ae (Lp.coeFn_smul c u)] with z hz hscale hu hc
        simp only [hz, hscale, Pi.smul_apply, hu, hc, smul_eq_mul]
        ring }
  exact A.mkContinuous ‖f‖ fun u => (norm_tensorLp f u).le

private theorem tensorRight_apply (f : Lp ℝ 2 m) (g : Lp ℝ 2 n) :
    tensorRight f g = tensorLp f g := rfl

/-- Taking the first-variable pairing of a square-integrable kernel
against a fixed square-integrable function is an actual bounded map.
Adjunction defines the resulting second-variable L² class. -/
def tensorCoefficient (f : Lp ℝ 2 m) : Lp ℝ 2 (m.prod n) →L[ℝ] Lp ℝ 2 n :=
  (tensorRight f).adjoint

theorem tensorCoefficient_inner (f : Lp ℝ 2 m) (Q : Lp ℝ 2 (m.prod n)) (g : Lp ℝ 2 n) :
    inner ℝ (tensorCoefficient f Q) g = inner ℝ Q (tensorLp f g) := by
  rw [tensorCoefficient, ContinuousLinearMap.adjoint_inner_left, tensorRight_apply]

theorem norm_tensorCoefficient_le (f : Lp ℝ 2 m) (Q : Lp ℝ 2 (m.prod n)) :
    ‖tensorCoefficient f Q‖ ≤ ‖f‖ * ‖Q‖ := by
  have h : ‖tensorRight (n := n) f‖ ≤ ‖f‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    intro g
    rw [tensorRight_apply, norm_tensorLp]
  apply ((tensorCoefficient f).le_opNorm Q).trans
  rw [tensorCoefficient, ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg Q)

theorem tensorCoefficient_inner_integral (f : Lp ℝ 2 m) (Q : Lp ℝ 2 (m.prod n)) (g : Lp ℝ 2 n) :
    inner ℝ (tensorCoefficient f Q) g =
      ∫ x, f x * (∫ y, Q (x,y) * g y ∂n) ∂m := by
  rw [tensorCoefficient_inner, L2.inner_def]
  have he : (fun z => inner ℝ (Q z) ((tensorLp f g : Lp ℝ 2 (m.prod n)) z)) =ᵐ[m.prod n]
      (fun z : α × β => f z.1 * (Q z * g z.2)) := by
    filter_upwards [tensorLp_ae f g] with z hz
    rw [hz, RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae he]
  have hI : Integrable (fun z : α × β => f z.1 * (Q z * g z.2)) (m.prod n) :=
    (L2.integrable_inner (𝕜 := ℝ) Q (tensorLp f g)).congr he
  rw [integral_prod _ hI]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => integral_const_mul (f x) _

/-- The Hilbert adjoint coefficient has the manuscript's integral
representative on finite-volume second arms. -/
theorem tensorCoefficient_ae_integral [IsFiniteMeasure n]
    (f : Lp ℝ 2 m) (Q : Lp ℝ 2 (m.prod n)) :
    (tensorCoefficient f Q : β → ℝ) =ᵐ[n] fun y => ∫ x, f x * Q (x,y) ∂m := by
  have hL : MemLp (fun z : α × β => f z.1) 2 (m.prod n) :=
    (Lp.memLp f).comp_fst n
  have hI : Integrable (fun z : α × β => f z.1 * Q z) (m.prod n) := by
    refine (L2.integrable_inner (𝕜 := ℝ) Q (hL.toLp _)).congr ?_
    filter_upwards [hL.coeFn_toLp] with z hz
    rw [RCLike.inner_apply, conj_trivial, hz]
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp (tensorCoefficient f Q)).integrable (by norm_num)) hI.integral_prod_right ?_
  intro s hs hns
  let g : Lp ℝ 2 n := indicatorConstLp 2 hs hns.ne 1
  have hgae : (g : β → ℝ) =ᵐ[n] s.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
  have hinner : inner ℝ (tensorCoefficient f Q) g =
      ∫ y in s, tensorCoefficient f Q y ∂n := by
    rw [L2.inner_def, ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [hgae] with y hy
    rw [RCLike.inner_apply, conj_trivial, hy]
    by_cases hys : y ∈ s <;> simp [hys]
  rw [← hinner, tensorCoefficient_inner, L2.inner_def]
  have he : (fun z => inner ℝ (Q z) ((tensorLp f g : Lp ℝ 2 (m.prod n)) z)) =ᵐ[m.prod n]
      (fun z => s.indicator (fun _ => f z.1 * Q z) z.2) := by
    filter_upwards [tensorLp_ae f g, Measure.quasiMeasurePreserving_snd.ae hgae] with z hz hz'
    change g z.2 = s.indicator (fun _ => (1 : ℝ)) z.2 at hz'
    rw [RCLike.inner_apply, conj_trivial, hz, hz']
    by_cases hzs : z.2 ∈ s <;> simp [hzs]
  rw [integral_congr_ae he, integral_prod_symm _ ((L2.integrable_inner (𝕜 := ℝ) Q
    (tensorLp f g)).congr he), ← integral_indicator hs]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    by_cases hys : y ∈ s <;> simp [hys]

/-- Fubini for L² classes supplies an actual L² slice almost everywhere. -/
theorem ae_memLp_left_of_prod (Q : Lp ℝ 2 (m.prod n)) :
    ∀ᵐ y ∂n, MemLp (fun x => Q (x,y)) 2 m := by
  filter_upwards [(Lp.aestronglyMeasurable Q).prodMk_right,
    (Lp.memLp Q).integrable_sq.prod_left_ae] with y hm hI
  exact (memLp_two_iff_integrable_sq hm).mpr hI

theorem ae_memLp_right_of_prod (Q : Lp ℝ 2 (m.prod n)) :
    ∀ᵐ x ∂m, MemLp (fun y => Q (x,y)) 2 n := by
  filter_upwards [(Lp.aestronglyMeasurable Q).prodMk_left,
    (Lp.memLp Q).integrable_sq.prod_right_ae] with x hm hI
  exact (memLp_two_iff_integrable_sq hm).mpr hI

end LocalMetricExtension
