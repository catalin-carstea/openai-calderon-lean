import Proof.HessianCoordinateBounds
import Proof.CoordinateHigherNorms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def coordinateTensorThreeL (T : (Fin 3 → I) → ℝ) : X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ :=
  ∑ b,T b • (EuclideanSpace.proj (b 0)).smulRight
    ((EuclideanSpace.proj (b 1)).smulRight (EuclideanSpace.proj (b 2)))

lemma coordinateTensorThreeL_apply (T : (Fin 3 → I) → ℝ) (u v w : X) :
    coordinateTensorThreeL T u v w = ∑ b,T b*u (b 0)*v (b 1)*w (b 2) := by
  simp only [coordinateTensorThreeL,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma coordinateTensorThreeL_axes (T : (Fin 3 → I) → ℝ) (i j k : I) :
    coordinateTensorThreeL T (axis i) (axis j) (axis k) = T ![i,j,k] := by
  classical
  rw [coordinateTensorThreeL_apply]
  rw [Finset.sum_eq_single ![i,j,k]]
  · simp [axis]
  · intro b _ hne
    by_cases h0 : b 0 = i
    · by_cases h1 : b 1 = j
      · by_cases h2 : b 2 = k
        · exact False.elim (hne (by ext t;fin_cases t <;> simp [h0,h1,h2]))
        · simp [axis,h2]
      · simp [axis,h1]
    · simp [axis,h0]
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

def framedCovJet (g : MetricField) (e : Frame) (f : X → ℝ) (n : ℕ) (y : X) (a : Fin n → I) : ℝ :=
  ∑ b,covJet g f n y b*∏ t,e y (a t) (b t)

lemma abs_framedCovJet_le_jetNorm (g : MetricField) (e : Frame) (f : X → ℝ) (n : ℕ) (y : X) (a : Fin n → I) :
    |framedCovJet g e f n y a| ≤ jetNorm g e f n y := by
  unfold jetNorm
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs,framedCovJet] using
    (Finset.single_le_sum (f:=fun a : Fin n → I => (framedCovJet g e f n y a)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ a))

lemma coordinateTensorThreeL_frame (g : MetricField) (e : Frame) (f : X → ℝ) (y : X) (i j k : I) :
    coordinateTensorThreeL (covJet g f 3 y) (e y i) (e y j) (e y k) = framedCovJet g e f 3 y ![i,j,k] := by
  rw [coordinateTensorThreeL_apply]
  unfold framedCovJet
  simp only [Fin.prod_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A pointwise trilinear tensor bound in an arbitrary orthonormal frame
controls each coordinate component. Only frame values enter the estimate. -/
theorem Elliptic.trilinear_entry_bound_of_frame {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (L : X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hFrame : ∀ p q r : I,|L (e y p) (e y q) (e y r)| ≤ B) (i j k : I) :
    |L (axis i) (axis j) (axis k)| ≤ 27*K^3*B := by
  let a : I → I → ℝ := fun s p => metricPair g y (axis s) (e y p)
  have hFirst := linear_frame_expansion g e y he ((L.flip (axis j)).flip (axis k)) (axis i)
  change L (axis i) (axis j) (axis k) = ∑ p,a i p*L (e y p) (axis j) (axis k) at hFirst
  have hSecond (p : I) := linear_frame_expansion g e y he ((L (e y p)).flip (axis k)) (axis j)
  change ∀ p : I,L (e y p) (axis j) (axis k) = ∑ q,a j q*L (e y p) (e y q) (axis k) at hSecond
  have hThird (p q : I) := linear_frame_expansion g e y he (L (e y p) (e y q)) (axis k)
  change ∀ p q : I,L (e y p) (e y q) (axis k) = ∑ r,a k r*L (e y p) (e y q) (e y r) at hThird
  have hExpand : L (axis i) (axis j) (axis k) =
      ∑ p,∑ q,∑ r,a i p*a j q*a k r*L (e y p) (e y q) (e y r) := by
    rw [hFirst]
    simp_rw [hSecond,hThird,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hTerm (p q r : I) : ‖a i p*a j q*a k r*L (e y p) (e y q) (e y r)‖ ≤ K^3*B := by
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul]
    calc
      _ ≤ K*K*K*B := by
        gcongr
        · exact h.frame_coordinate_abs_bound hK e hy he i p
        · exact h.frame_coordinate_abs_bound hK e hy he j q
        · exact h.frame_coordinate_abs_bound hK e hy he k r
        · exact hFrame p q r
      _ = _ := by ring
  rw [hExpand]
  have hSum := norm_fin3_triple_sum_le
    (fun p q r => a i p*a j q*a k r*L (e y p) (e y q) (e y r)) (K^3*B) hTerm
  simpa only [Real.norm_eq_abs,mul_assoc] using hSum

lemma Elliptic.covJet_three_coordinate_bound {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (f : X → ℝ) (i j k : I) :
    |covJet g f 3 y ![i,j,k]| ≤ 27*K^3*jetNorm g e f 3 y := by
  have hT := h.trilinear_entry_bound_of_frame hK e hy he (coordinateTensorThreeL (covJet g f 3 y))
    (jetNorm g e f 3 y) (Real.sqrt_nonneg _) (by
      intro p q r
      rw [coordinateTensorThreeL_frame]
      exact abs_framedCovJet_le_jetNorm g e f 3 y ![p,q,r]) i j k
  simpa only [coordinateTensorThreeL_axes] using hT

/-- The third covariant log-radius tensor has a coordinate budget for
EVERY admitted radius and frame, with no frame-derivative assumption. -/
lemma Profile.coordinate_third_covariant_bound {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) (i j k : I) :
    |covJet g (fun x => Real.log (r x)) 3 y ![i,j,k]| ≤
      27*K^3*|Cj 3| *(beta g r y)^3 := by
  have hBeta : 0 ≤ beta g r y := Real.sqrt_nonneg _
  have hJet := (hp.2 y hy).2.2.2 (3:Fin 9) (by decide)
  have hJet' : jetNorm g e (fun x => Real.log (r x)) 3 y ≤ |Cj 3| *(beta g r y)^3 :=
    hJet.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  exact (h.covJet_three_coordinate_bound hK e hy (hframe y hy) _ i j k).trans
    ((mul_le_mul_of_nonneg_left hJet' (by positivity)).trans_eq (by ring))

end ShrinkingSpheres
