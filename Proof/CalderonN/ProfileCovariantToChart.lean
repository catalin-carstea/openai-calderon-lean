module

public import Proof.CalderonN.TraceFrameCoefficients
public import Proof.CalderonN.ProfileCovariant

import Mathlib.Tactic

/-! Recover every chart component of a covariant derivative from its
protected orthonormal-frame norm. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem traceFrameCoordinate_reconstruct_axis (g : MetricField dim) (e : Frame dim)
    (x : X dim) (he : ∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (i j : I dim) :
    (∑ a : I dim,traceFrameCoordinate g e a i x*e x a j) = if i=j then 1 else 0 := by
  classical
  have hv := frameVectorL_frameCoordinatesL g x (e x) he (axis i)
  rw [frameVectorL_apply (e x) _ x] at hv
  have hi := congrArg (EuclideanSpace.proj (𝕜:=ℝ) j) hv
  change (EuclideanSpace.proj (𝕜:=ℝ) j) (∑ a : I dim,
    (traceFrameCoordinate g e a i x) • e x a) = (EuclideanSpace.proj (𝕜:=ℝ) j) (axis i) at hi
  simpa only [map_sum,map_smul,PiLp.proj_apply,smul_eq_mul,axis,PiLp.single_apply,eq_comm] using hi

theorem abs_traceFrameCoordinate_le {Y : Set (X dim)} {K : ℝ} {g : MetricField dim} {e : Frame dim}
    (hg : Elliptic Y K g) {x : X dim} (hx : x ∈ Y)
    (he : ∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0) (a i : I dim) :
    |traceFrameCoordinate g e a i x| ≤ Real.sqrt K := by
  have h := PiLp.norm_apply_le (frameCoordinatesL g x (e x) (axis i)) a
  have hsq : ‖frameCoordinatesL g x (e x) (axis i)‖^2 ≤ K := by
    rw [frameCoordinatesL_apply,norm_frameCoordinates_sq _ _ _ _ he]
    simpa only [norm_axis,one_pow,mul_one] using (hg.2 x hx).2 (axis i) |>.2
  have h' : |traceFrameCoordinate g e a i x| ≤ ‖frameCoordinatesL g x (e x) (axis i)‖ := by
    simpa only [traceFrameCoordinate,Real.norm_eq_abs] using h
  exact h'.trans (Real.le_sqrt_of_sq_le hsq)

theorem covJet_eq_frame_components (g : MetricField dim) (e : Frame dim)
    (x : X dim) (he : ∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (f : X dim → ℝ) (n : ℕ) (i : Fin n → I dim) :
    covJet g f n x i = ∑ a : Fin n → I dim,
      (∏ t : Fin n,traceFrameCoordinate g e (a t) (i t) x)*
      (∑ b : Fin n → I dim,covJet g f n x b*∏ t : Fin n,e x (a t) (b t)) := by
  classical
  let H (t : Fin n) (a b : I dim) := traceFrameCoordinate g e a (i t) x*e x a b
  have hProd (a b : Fin n → I dim) :
      (∏ t : Fin n,traceFrameCoordinate g e (a t) (i t) x)*
        (covJet g f n x b*∏ t : Fin n,e x (a t) (b t)) =
      covJet g f n x b*∏ t : Fin n,H t (a t) (b t) := by
    simp only [H,Finset.prod_mul_distrib]
    ring
  simp_rw [Finset.mul_sum,hProd]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have hSum (b : Fin n → I dim) : (∑ a : Fin n → I dim,∏ t : Fin n,H t (a t) (b t)) =
      if i=b then 1 else 0 := by
    rw [← Fintype.prod_sum (fun t a => H t a (b t))]
    change (∏ t : Fin n,∑ a : I dim,traceFrameCoordinate g e a (i t) x*e x a (b t)) = _
    simp only [traceFrameCoordinate_reconstruct_axis g e x he]
    by_cases h : i=b
    · subst b
      simp
    · have hAt : ∃ t : Fin n,i t ≠ b t := by
        by_contra! hAll
        exact h (funext hAll)
      obtain ⟨t,ht⟩ := hAt
      rw [if_neg h,Finset.prod_eq_zero (Finset.mem_univ t)]
      exact if_neg ht
  simp only [hSum,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem abs_covJet_chart_le {Y : Set (X dim)} {K : ℝ} {g : MetricField dim} {e : Frame dim}
    (hg : Elliptic Y K g) {x : X dim} (hx : x ∈ Y)
    (he : ∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (f : X dim → ℝ) (n : ℕ) (i : Fin n → I dim) :
    |covJet g f n x i| ≤ ((dim:ℝ)*Real.sqrt K)^n*jetNorm g e f n x := by
  let F (a : Fin n → I dim) := ∑ b : Fin n → I dim,covJet g f n x b*∏ t : Fin n,e x (a t) (b t)
  let H (a : Fin n → I dim) := ∏ t : Fin n,traceFrameCoordinate g e (a t) (i t) x
  have hF (a : Fin n → I dim) : |F a| ≤ jetNorm g e f n x := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum
      (f := fun t : Fin n → I dim => (F t)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a))
  have hH (a : Fin n → I dim) : |H a| ≤ (Real.sqrt K)^n := by
    simp only [H,Finset.abs_prod]
    calc
      _ ≤ ∏ _t : Fin n, Real.sqrt K := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun _ _ => abs_traceFrameCoordinate_le hg hx he _ _)
      _ = _ := by simp
  rw [covJet_eq_frame_components g e x he f n i]
  change |∑ a : Fin n → I dim,H a*F a| ≤ _
  calc
    _ ≤ ∑ a : Fin n → I dim,|H a*F a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n → I dim,(Real.sqrt K)^n*jetNorm g e f n x := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul (hH a) (hF a) (abs_nonneg _) (by positivity)
    _ = _ := by
      simp [mul_pow,mul_assoc]

end CalderonN
