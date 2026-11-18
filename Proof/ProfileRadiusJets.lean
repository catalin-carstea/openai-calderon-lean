import Proof.FrameBasis
import Proof.FrameDuality
import Proof.MovingRadius
import Proof.InverseMetricBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma linear_frame_expansion (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (L : X →L[ℝ] ℝ) (v : X) :
    L v = ∑ i,metricPair g y v (e y i)*L (e y i) := by
  have h := congrArg L ((frameBasis g e y he).sum_repr v)
  simpa only [map_sum,map_smul,frameBasis_apply,frameBasis_repr,smul_eq_mul] using h.symm

lemma sum_frame_coordinates_sq (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (v : X) :
    (∑ i,(metricPair g y v (e y i))^2) = metricPair g y v v := by
  let z : X := WithLp.toLp 2 (fun i => metricPair g y v (e y i))
  have hrec : frameVector e y z = v := by
    simpa only [frameVector,frameBasis_apply,frameBasis_repr,z] using (frameBasis g e y he).sum_repr v
  have h := metricPair_frameVector g e y z z he
  rw [hrec] at h
  simpa only [z,WithLp.ofLp_toLp,pow_two] using h.symm

lemma covector_frame_cauchy (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (L : X →L[ℝ] ℝ) (v : X) :
    (L v)^2 ≤ metricPair g y v v*(∑ i,(L (e y i))^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => metricPair g y v (e y i)) (fun i => L (e y i))
  rw [← linear_frame_expansion g e y he L v,sum_frame_coordinates_sq g e y he v] at h
  exact h

lemma Elliptic.coord_logRadius_bound {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame) (r : X → ℝ) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (i : I) :
    |coordDeriv i (fun x => Real.log (r x)) y| ≤ K*beta g r y := by
  have hcs := covector_frame_cauchy g e y he (fderiv ℝ (fun x => Real.log (r x)) y) (axis i)
  rw [← beta_sq g e r y he] at hcs
  have hv := (h.2 y hy).2 (axis i) |>.2
  rw [norm_axis,one_pow,mul_one] at hv
  have hs : (coordDeriv i (fun x => Real.log (r x)) y)^2 ≤ K*(beta g r y)^2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hv (sq_nonneg _))
  have hKK : K ≤ K^2 := by nlinarith
  have ht := hs.trans (mul_le_mul_of_nonneg_right hKK (sq_nonneg (beta g r y)))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (zero_le_one.trans hK) (Real.sqrt_nonneg _))).mp
  simpa only [sq_abs,mul_pow,beta] using ht

/-- Every admitted radius has the first coordinate jet required by the coefficient
    weight calculus, with a constant from ellipticity alone. -/
theorem Profile.coordinate_radius_first_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) (i : I) : |coordDeriv i r y| ≤ K*r y*beta g r y := by
  have hd := ((hp.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hpos := (hp.2 y hy).1
  have hl := logRadius_derivative r y (axis i) hd hpos.ne'
  have heq : coordDeriv i r y = r y*coordDeriv i (fun x => Real.log (r x)) y := by
    change fderiv ℝ r y (axis i) = r y*fderiv ℝ (fun x => Real.log (r x)) y (axis i)
    rw [hl,← mul_assoc,mul_inv_cancel₀ hpos.ne',one_mul]
  rw [heq,abs_mul,abs_of_pos hpos]
  have hb := mul_le_mul_of_nonneg_left (h.coord_logRadius_bound hK e r hy (hframe y hy) i) hpos.le
  nlinarith only [hb]

end ShrinkingSpheres
