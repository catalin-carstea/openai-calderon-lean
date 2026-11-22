module

public import Proof.CalderonN.HessianDifferential
public import Proof.CalderonN.MetricSmooth
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

@[expose] public section

/- Port of GradientDivergence.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

variable [NeZero n]
open Set


/-- The metric gradient expressed in the chosen orthonormal frame. -/
def metricGradient (e : (Frame n)) (f : (X n) → ℝ) (y : (X n)) : (X n) :=
  ∑ i, fderiv ℝ f y (e y i) • e y i

lemma metricGradient_duality (g : (MetricField n)) (e : (Frame n)) (f : (X n) → ℝ) (y v : (X n))
    (hs : (g y).transpose = g y)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    metricPair g y (metricGradient e f y) v = fderiv ℝ f y v := by
  have hh := congrArg (fderiv ℝ f y) ((frameBasis g e y he).sum_repr v)
  simp only [map_sum, map_smul, frameBasis_apply, frameBasis_repr, smul_eq_mul] at hh
  unfold metricGradient
  rw [metricPair_sum_left]
  simp only [metricPair_smul_left]
  calc
    _ = ∑ i, metricPair g y v (e y i) * fderiv ℝ f y (e y i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [metricPair_symm g y _ _ hs]
      ring
    _ = _ := hh

lemma contDiffOn_metricGradient {Ω : Set (X n)} (hΩ : IsOpen Ω) (e : (Frame n)) (f : (X n) → ℝ)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (metricGradient e f) Ω :=
  ContDiffOn.sum (fun i _ => (((hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).clm_apply (he i)).smul (he i)))

/-- Differentiating gradient duality turns covariant differentiation of the metric gradient
    into the Hessian bilinear form. -/
lemma metricGradient_covariant_pair {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (f : (X n) → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) {y : (X n)} (hy : y ∈ Ω) (a v : (X n)) :
    metricPair g y (fderiv ℝ (metricGradient e f) y a + connection g y a (metricGradient e f y)) v =
      hessianBilinear g f y a v := by
  have hG := ((contDiffOn_metricGradient hΩ e f he hf).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hf₂ := ((hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hfun : (fun x => metricPair g x (metricGradient e f x) v) =ᶠ[nhds y]
      (fun x => fderiv ℝ f x v) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact metricGradient_duality g e f x v (h.2 x hx).1 (hframe x hx)
  have hh := congrArg (fun L : (X n) →L[ℝ] ℝ => L a) hfun.fderiv_eq
  rw [metric_pair_fderiv hΩ h hy _ (fun _ => v) hG (differentiableAt_const _),
    derivative_covector_apply f y a v hf₂] at hh
  have hz : metricPair g y (metricGradient e f y) (0:(X n)) = 0 := by simp [metricPair]
  simp only [fderiv_const_apply, zero_apply] at hh
  rw [hz] at hh
  have hm := connection_metric hΩ h hK hy a (metricGradient e f y) v
  have hd := metricGradient_duality g e f y (connection g y a v) (h.2 y hy).1 (hframe y hy)
  rw [hessianBilinear_apply]
  simp only [← metricBilinear_apply, map_add, _root_.add_apply] at hh hm hd ⊢
  linarith

lemma weightedDivergence_gradient_hessian {Ω : Set (X n)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (f : (X n) → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) {y : (X n)} (hy : y ∈ Ω) :
    weightedDivergence (metricDensity g) (metricGradient e f) y =
      metricDensity g y * ∑ i, frameHessian g e f y i i := by
  have hG := ((contDiffOn_metricGradient hΩ e f he hf).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hf₂ := ((hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  rw [weightedDivergence_metric_frame hΩ h hK e hy (hframe y hy) _ hG]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [metricGradient_covariant_pair hΩ h hK e he hframe f hf hy,
    hessianBilinear_eq_coordinate g f y hf₂]
  rfl

lemma profile_gradient_divergence_bound {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ x ∈ Y, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : (X n)} (hy : y ∈ Y) :
    weightedDivergence (metricDensity g) (metricGradient e (fun x => Real.log (r x))) y ≤
      metricDensity g y * (-(n : ℝ)*c₀*beta g r y) := by
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  rw [weightedDivergence_gradient_hessian hY h hK e he hframe _ hf hy]
  exact mul_le_mul_of_nonneg_left (hp.frame_trace hy (hframe y hy)) (metricDensity_pos h hK hy).le

end CalderonN
