import Proof.HessianDifferential
import Proof.MetricSmooth

noncomputable section
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The metric gradient expressed in the chosen orthonormal frame. -/
def metricGradient (e : Frame) (f : X → ℝ) (y : X) : X :=
  ∑ i, fderiv ℝ f y (e y i) • e y i

lemma metricGradient_duality (g : MetricField) (e : Frame) (f : X → ℝ) (y v : X)
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

lemma contDiffOn_metricGradient {Ω : Set X} (hΩ : IsOpen Ω) (e : Frame) (f : X → ℝ)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω) (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (metricGradient e f) Ω :=
  ContDiffOn.sum (fun i _ => (((hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).clm_apply (he i)).smul (he i)))

/-- Differentiating gradient duality turns covariant differentiation of the metric gradient
    into the Hessian bilinear form. -/
lemma metricGradient_covariant_pair {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) (a v : X) :
    metricPair g y (fderiv ℝ (metricGradient e f) y a + connection g y a (metricGradient e f y)) v =
      hessianBilinear g f y a v := by
  have hG := ((contDiffOn_metricGradient hΩ e f he hf).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hf₂ := ((hf.fderiv_of_isOpen (m := ∞) hΩ (by simp)).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hfun : (fun x => metricPair g x (metricGradient e f x) v) =ᶠ[nhds y]
      (fun x => fderiv ℝ f x v) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact metricGradient_duality g e f x v (h.2 x hx).1 (hframe x hx)
  have hh := congrArg (fun L : X →L[ℝ] ℝ => L a) hfun.fderiv_eq
  rw [metric_pair_fderiv hΩ h hy _ (fun _ => v) hG (differentiableAt_const _),
    derivative_covector_apply f y a v hf₂] at hh
  have hz : metricPair g y (metricGradient e f y) (0:X) = 0 := by simp [metricPair]
  simp only [fderiv_const_apply, zero_apply] at hh
  rw [hz] at hh
  have hm := connection_metric hΩ h hK hy a (metricGradient e f y) v
  have hd := metricGradient_duality g e f y (connection g y a v) (h.2 y hy).1 (hframe y hy)
  rw [hessianBilinear_apply]
  simp only [← metricBilinear_apply, map_add, _root_.add_apply] at hh hm hd ⊢
  linarith

lemma weightedDivergence_gradient_hessian {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f Ω) {y : X} (hy : y ∈ Ω) :
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

lemma profile_gradient_divergence_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ x ∈ Y, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) :
    weightedDivergence (metricDensity g) (metricGradient e (fun x => Real.log (r x))) y ≤
      metricDensity g y * (-3*c₀*beta g r y) := by
  have hf : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  rw [weightedDivergence_gradient_hessian hY h hK e he hframe _ hf hy]
  exact mul_le_mul_of_nonneg_left (hp.frame_trace hy (hframe y hy)) (metricDensity_pos h hK hy).le

end ShrinkingSpheres
