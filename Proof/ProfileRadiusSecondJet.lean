import Proof.HessianCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma Profile.coordinate_log_second_bound {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {G : ℝ} (hG : 0 ≤ G) {y : X} (hy : y ∈ Y) (hΓ : ∀ k i j,|christoffel g y k i j| ≤ G) (i j : I) :
    |coordDeriv i (coordDeriv j (fun x => Real.log (r x))) y| ≤
      (9*K^2*|Cj 2|+3*G*K)*(beta g r y)^2 := by
  have hb : 1 ≤ beta g r y := hf.trans (hp.2 y hy).2.1
  have hb0 : 0 ≤ beta g r y := zero_le_one.trans hb
  have hc := hp.coordinate_hessian_bound h hK e hframe hy i j
  have ht (k : I) : |christoffel g y k i j*coordDeriv k (fun x => Real.log (r x)) y| ≤ G*(K*beta g r y) := by
    rw [abs_mul]
    exact mul_le_mul (hΓ k i j) (h.coord_logRadius_bound hK e r hy (hframe y hy) k) (abs_nonneg _) hG
  have hs : |∑ k,christoffel g y k i j*coordDeriv k (fun x => Real.log (r x)) y| ≤ 3*G*K*beta g r y := by
    calc
      _ ≤ ∑ k,|christoffel g y k i j*coordDeriv k (fun x => Real.log (r x)) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : I,G*(K*beta g r y) := Finset.sum_le_sum (fun k _ => ht k)
      _ = _ := by simp [I]; ring
  have heq : coordDeriv i (coordDeriv j (fun x => Real.log (r x))) y =
      covJet g (fun x => Real.log (r x)) 2 y ![i,j]+
        ∑ k,christoffel g y k i j*coordDeriv k (fun x => Real.log (r x)) y := by
    rw [covJet_two]
    ring
  rw [heq]
  have hbb : beta g r y ≤ (beta g r y)^2 := by nlinarith
  have hconn := mul_le_mul_of_nonneg_left hbb (show 0 ≤ 3*G*K by positivity)
  exact (abs_add_le _ _).trans (by nlinarith only [hc,hs,hconn])

lemma Profile.coordinate_radius_first_identity {Y : Set X} (hY : IsOpen Y) {g : MetricField} {e : Frame}
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) (i : I) :
    coordDeriv i r y = r y*coordDeriv i (fun x => Real.log (r x)) y := by
  have hl := logRadius_derivative r y (axis i) ((hp.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) (hp.2 y hy).1.ne'
  change fderiv ℝ r y (axis i) = r y*fderiv ℝ (fun x => Real.log (r x)) y (axis i)
  rw [hl,← mul_assoc,mul_inv_cancel₀ (hp.2 y hy).1.ne',one_mul]

lemma Profile.coordinate_radius_second_identity {Y : Set X} (hY : IsOpen Y) {g : MetricField} {e : Frame}
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) (i j : I) :
    coordDeriv i (coordDeriv j r) y = r y*(coordDeriv i (fun x => Real.log (r x)) y*
      coordDeriv j (fun x => Real.log (r x)) y+coordDeriv i (coordDeriv j (fun x => Real.log (r x))) y) := by
  have hl : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y := hp.1.log (fun x hx => (hp.2 x hx).1.ne')
  have hdf : ContDiffOn ℝ ∞ (coordDeriv j (fun x => Real.log (r x))) Y :=
    (hl.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have heq : coordDeriv j r =ᶠ[𝓝 y] (fun x => r x*coordDeriv j (fun x => Real.log (r x)) x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hp.coordinate_radius_first_identity hY hx j
  have hr := (hp.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hd := (hdf.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hi : coordDeriv i (coordDeriv j r) y = coordDeriv i r y*coordDeriv j (fun x => Real.log (r x)) y+
      r y*coordDeriv i (coordDeriv j (fun x => Real.log (r x))) y := by
    change (fderiv ℝ (coordDeriv j r) y) (axis i) = _
    rw [heq.fderiv_eq,(hr.hasFDerivAt.fun_mul hd.hasFDerivAt).fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,coordDeriv]
    ring
  rw [hi,hp.coordinate_radius_first_identity hY hy i]
  ring

/-- The two-jet radius estimate needed by the scalar-principal coefficient calculus holds
    for every admitted radius. No special shrinking profile is substituted. -/
theorem Profile.coordinate_radius_second_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {G : ℝ} (hG : 0 ≤ G) {y : X} (hy : y ∈ Y) (hΓ : ∀ k i j,|christoffel g y k i j| ≤ G) (i j : I) :
    |coordDeriv i (coordDeriv j r) y| ≤ (K^2+9*K^2*|Cj 2|+3*G*K)*r y*(beta g r y)^2 := by
  have hr := (hp.2 y hy).1
  have hi := h.coord_logRadius_bound hK e r hy (hframe y hy) i
  have hj := h.coord_logRadius_bound hK e r hy (hframe y hy) j
  have hsecond := hp.coordinate_log_second_bound h hK e hframe hf hG hy hΓ i j
  have hprod := mul_le_mul hi hj (abs_nonneg _) (mul_nonneg (zero_le_one.trans hK) (Real.sqrt_nonneg _))
  rw [hp.coordinate_radius_second_identity hY hy i j,abs_mul,abs_of_pos hr]
  have hprod' : |coordDeriv i (fun x => Real.log (r x)) y*coordDeriv j (fun x => Real.log (r x)) y| ≤
      (K*beta g r y)^2 := by
    rw [abs_mul]
    simpa only [pow_two] using hprod
  have hsum := (abs_add_le _ _).trans (add_le_add hprod' hsecond)
  have ht := mul_le_mul_of_nonneg_left hsum hr.le
  nlinarith only [ht]

end ShrinkingSpheres
