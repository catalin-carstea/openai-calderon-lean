import Proof.ProfileRadiusJets
import Proof.HessianDifferential
import Proof.ProfileHessian
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma sum_fin_two_indices (f : (Fin 2 → I) → ℝ) :
    (∑ a,f a) = ∑ i,∑ j,f ![i,j] := by
  calc
    _ = ∑ p : I × I,f ![p.1,p.2] := Fintype.sum_equiv (finTwoArrowEquiv I) _ _ (fun a => by
      congr 1
      ext t
      fin_cases t <;> rfl)
    _ = _ := Fintype.sum_prod_type _

lemma jetNorm_two_sq (g : MetricField) (e : Frame) (f : X → ℝ) (y : X) :
    (jetNorm g e f 2 y)^2 = ∑ i,∑ j,(frameHessian g e f y i j)^2 := by
  rw [jetNorm,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [sum_fin_two_indices]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_fin_two_indices]
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,frameHessian,hessianMatrix,metricPair,mul_assoc]

lemma frameHessian_abs_le_jetNorm (g : MetricField) (e : Frame) (f : X → ℝ) (y : X) (i j : I) :
    |frameHessian g e f y i j| ≤ jetNorm g e f 2 y := by
  have h : (frameHessian g e f y i j)^2 ≤ ∑ i,∑ j,(frameHessian g e f y i j)^2 :=
    (Finset.single_le_sum (f:=fun k : I => (frameHessian g e f y i k)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f:=fun k : I => ∑ l,(frameHessian g e f y k l)^2)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i))
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  change |frameHessian g e f y i j|^2 ≤ (jetNorm g e f 2 y)^2
  rw [sq_abs,jetNorm_two_sq]
  exact h

lemma Elliptic.frame_coordinate_abs_bound {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (i j : I) :
    |metricPair g y (axis i) (e y j)| ≤ K := by
  have hs : (metricPair g y (axis i) (e y j))^2 ≤ metricPair g y (axis i) (axis i) := by
    rw [← sum_frame_coordinates_sq g e y he]
    exact Finset.single_le_sum (f:=fun k : I => (metricPair g y (axis i) (e y k))^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hv := (h.2 y hy).2 (axis i) |>.2
  rw [norm_axis,one_pow,mul_one] at hv
  have hKK : K ≤ K^2 := by nlinarith
  apply (sq_le_sq₀ (abs_nonneg _) (zero_le_one.trans hK)).mp
  simpa only [sq_abs] using hs.trans (hv.trans hKK)

lemma Elliptic.matrix_entry_bound_of_frame {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (A : MetricField) {B : ℝ} (hB : 0 ≤ B) (hframe : ∀ p q,|metricPair A y (e y p) (e y q)| ≤ B) (i j : I) :
    |A y i j| ≤ 9*K^2*B := by
  let zi : X := WithLp.toLp 2 (fun p => metricPair g y (axis i) (e y p))
  let zj : X := WithLp.toLp 2 (fun p => metricPair g y (axis j) (e y p))
  have hreci : frameVector e y zi = axis i := by
    simpa only [zi,frameVector,frameBasis_apply,frameBasis_repr] using (frameBasis g e y he).sum_repr (axis i)
  have hrecj : frameVector e y zj = axis j := by
    simpa only [zj,frameVector,frameBasis_apply,frameBasis_repr] using (frameBasis g e y he).sum_repr (axis j)
  have heq : A y i j = ∑ p,∑ q,metricPair A y (e y p) (e y q)*zi p*zj q := by
    rw [← metricPair_frame_expansion A e y zi zj,hreci,hrecj]
    simp [metricPair,axis]
  rw [heq]
  calc
    _ ≤ ∑ p,∑ q,|metricPair A y (e y p) (e y q)*zi p*zj q| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _p : I,∑ _q : I,B*K*K := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hframe p q) (h.frame_coordinate_abs_bound hK e hy he i p)
        (abs_nonneg _) hB) (h.frame_coordinate_abs_bound hK e hy he j q) (abs_nonneg _) (mul_nonneg hB (zero_le_one.trans hK))
    _ = _ := by simp [I]; ring

lemma Profile.coordinate_hessian_bound {Y : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    {y : X} (hy : y ∈ Y) (i j : I) :
    |covJet g (fun x => Real.log (r x)) 2 y ![i,j]| ≤ 9*K^2*|Cj 2| *(beta g r y)^2 := by
  have hjet := (hp.2 y hy).2.2.2 (2 : Fin 9) (by decide)
  have hjet' : jetNorm g e (fun x => Real.log (r x)) 2 y ≤ |Cj 2| *(beta g r y)^2 :=
    hjet.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have hb := h.matrix_entry_bound_of_frame hK e hy (hframe y hy) (hessianMatrix g (fun x => Real.log (r x)))
    (mul_nonneg (abs_nonneg (Cj 2)) (sq_nonneg (beta g r y)))
    (fun p q => (frameHessian_abs_le_jetNorm g e (fun x => Real.log (r x)) y p q).trans hjet') i j
  simpa only [hessianMatrix,mul_assoc] using hb

end ShrinkingSpheres
