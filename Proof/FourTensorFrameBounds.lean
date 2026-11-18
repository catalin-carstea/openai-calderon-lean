import Proof.ThirdTensorFrameBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 1800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def coordinateTensorFourL (T : (Fin 4 → I) → ℝ) : X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ :=
  ∑ b,T b • (EuclideanSpace.proj (𝕜:=ℝ) (b 0)).smulRight
    ((EuclideanSpace.proj (𝕜:=ℝ) (b 1)).smulRight ((EuclideanSpace.proj (𝕜:=ℝ) (b 2)).smulRight (EuclideanSpace.proj (𝕜:=ℝ) (b 3))))

lemma coordinateTensorFourL_apply (T : (Fin 4 → I) → ℝ) (u v w z : X) :
    coordinateTensorFourL T u v w z = ∑ b,T b*u (b 0)*v (b 1)*w (b 2)*z (b 3) := by
  simp only [coordinateTensorFourL,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma coordinateTensorFourL_axes (T : (Fin 4 → I) → ℝ) (i j k l : I) :
    coordinateTensorFourL T (axis i) (axis j) (axis k) (axis l) = T ![i,j,k,l] := by
  classical
  rw [coordinateTensorFourL_apply]
  rw [Finset.sum_eq_single ![i,j,k,l]]
  · simp [axis]
  · intro b hb hne
    by_cases h0 : b 0 = i
    · by_cases h1 : b 1 = j
      · by_cases h2 : b 2 = k
        · by_cases h3 : b 3 = l
          · exact False.elim (hne (by ext t;fin_cases t <;> simp [h0,h1,h2,h3]))
          · simp [axis,h3]
        · simp [axis,h2]
      · simp [axis,h1]
    · simp [axis,h0]
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

lemma coordinateTensorFourL_frame (g : MetricField) (e : Frame) (f : X → ℝ) (y : X) (i j k l : I) :
    coordinateTensorFourL (covJet g f 4 y) (e y i) (e y j) (e y k) (e y l) = framedCovJet g e f 4 y ![i,j,k,l] := by
  rw [coordinateTensorFourL_apply]
  unfold framedCovJet
  simp only [Fin.prod_univ_succ]

  apply Finset.sum_congr rfl
  intro b hb
  change covJet g f 4 y b*e y i (b 0)*e y j (b 1)*e y k (b 2)*e y l (b 3) =
    covJet g f 4 y b*(e y i (b 0)*(e y j (b 1)*(e y k (b 2)*(e y l (b 3)*1))))
  ring

lemma Elliptic.fourlinear_entry_bound_of_frame {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (L : X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hFrame : ∀ p q r s : I,|L (e y p) (e y q) (e y r) (e y s)| ≤ B) (i j k l : I) :
    |L (axis i) (axis j) (axis k) (axis l)| ≤ 81*K^4*B := by
  let a : I → I → ℝ := fun s p => metricPair g y (axis s) (e y p)
  have hFirst := linear_frame_expansion g e y he (((L.flip (axis j)).flip (axis k)).flip (axis l)) (axis i)
  change L (axis i) (axis j) (axis k) (axis l) = ∑ p,a i p*L (e y p) (axis j) (axis k) (axis l) at hFirst
  have hSecond (p : I) := linear_frame_expansion g e y he (((L (e y p)).flip (axis k)).flip (axis l)) (axis j)
  change ∀ p : I,L (e y p) (axis j) (axis k) (axis l) = ∑ q,a j q*L (e y p) (e y q) (axis k) (axis l) at hSecond
  have hThird (p q : I) := linear_frame_expansion g e y he ((L (e y p) (e y q)).flip (axis l)) (axis k)
  change ∀ p q : I,L (e y p) (e y q) (axis k) (axis l) = ∑ r,a k r*L (e y p) (e y q) (e y r) (axis l) at hThird
  have hFourth (p q r : I) := linear_frame_expansion g e y he (L (e y p) (e y q) (e y r)) (axis l)
  change ∀ p q r : I,L (e y p) (e y q) (e y r) (axis l) = ∑ s,a l s*L (e y p) (e y q) (e y r) (e y s) at hFourth
  have hExpand : L (axis i) (axis j) (axis k) (axis l) =
      ∑ p,∑ q,∑ r,∑ s,a i p*a j q*a k r*a l s*L (e y p) (e y q) (e y r) (e y s) := by
    rw [hFirst]
    simp_rw [hSecond,hThird,hFourth,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hTerm (p q r s : I) :
      ‖a i p*a j q*a k r*a l s*L (e y p) (e y q) (e y r) (e y s)‖ ≤ K^4*B := by
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul,abs_mul]
    calc
      _ ≤ K*K*K*K*B := by
        gcongr
        · exact h.frame_coordinate_abs_bound hK e hy he i p
        · exact h.frame_coordinate_abs_bound hK e hy he j q
        · exact h.frame_coordinate_abs_bound hK e hy he k r
        · exact h.frame_coordinate_abs_bound hK e hy he l s
        · exact hFrame p q r s
      _ = _ := by ring
  rw [hExpand]
  have hSum : ‖∑ p,∑ q,∑ r,∑ s,a i p*a j q*a k r*a l s*L (e y p) (e y q) (e y r) (e y s)‖ ≤ 81*(K^4*B) := by
    calc
      _ ≤ ∑ p,‖∑ q,∑ r,∑ s,a i p*a j q*a k r*a l s*L (e y p) (e y q) (e y r) (e y s)‖ := norm_sum_le _ _
      _ ≤ ∑ _p : I,27*(K^4*B) := Finset.sum_le_sum (fun p hp => norm_fin3_triple_sum_le _ _ (hTerm p))
      _ = _ := by simp only [Fin.sum_univ_three];ring
  simpa only [Real.norm_eq_abs,mul_assoc] using hSum

lemma Elliptic.covJet_four_coordinate_bound {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (f : X → ℝ) (i j k l : I) :
    |covJet g f 4 y ![i,j,k,l]| ≤ 81*K^4*jetNorm g e f 4 y := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hh := h.fourlinear_entry_bound_of_frame hK e hy he (coordinateTensorFourL (covJet g f 4 y))
    (jetNorm g e f 4 y) (Real.sqrt_nonneg _) (fun p q r s => by
      rw [coordinateTensorFourL_frame]
      exact abs_framedCovJet_le_jetNorm g e f 4 y ![p,q,r,s]) i j k l
  simpa only [coordinateTensorFourL_axes] using hh

lemma Profile.coordinate_fourth_covariant_bound {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) (i j k l : I) :
    |covJet g (fun x => Real.log (r x)) 4 y ![i,j,k,l]| ≤
      81*K^4*|Cj 4| *(beta g r y)^4 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hBeta0 : 0 ≤ beta g r y := Real.sqrt_nonneg _
  have hJet := (hp.2 y hy).2.2.2 (4:Fin 9) (by decide)
  have hJet' : jetNorm g e (fun x => Real.log (r x)) 4 y ≤ |Cj 4| *(beta g r y)^4 :=
    hJet.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  exact (h.covJet_four_coordinate_bound hK e hy (hframe y hy) _ i j k l).trans
    ((mul_le_mul_of_nonneg_left hJet' (by positivity)).trans_eq (by ring))
end ShrinkingSpheres
