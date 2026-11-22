module

public import Proof.CalderonN.SphereFrameInvariant
public import Proof.CalderonN.Coercivity

import Mathlib.Algebra.BigOperators.Ring.Finset
import Proof.CalderonN.MetricConnection
import Proof.CalderonN.NormalBallChart
import Mathlib.Tactic

/-! Frame changes act orthogonally on each of the finite covector slots. -/

public section

noncomputable section
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sum_norm_sq_of_orthogonal_matrix (c : ι → ι → ℝ)
    (hc : ∀ i j, ∑ a, c a i*c a j = if i=j then 1 else 0) (x : ι → E) :
    (∑ a, ‖∑ i, c a i • x i‖^2) = ∑ i, ‖x i‖^2 := by
  have h (a i j : ι) : ⟪c a i • x i,c a j • x j⟫_ℝ = c a i*c a j*⟪x i,x j⟫_ℝ := by
    rw [real_inner_smul_left,real_inner_smul_right]
    ring
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum, h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hc]
  simp

private theorem prod_kronecker (m : ℕ) (i j : Fin m → ι) :
    (∏ t, if i t=j t then (1:ℝ) else 0) = if i=j then 1 else 0 := by
  classical
  by_cases h : i=j
  · simp [h]
  · obtain ⟨t,ht⟩ : ∃ t, i t ≠ j t := by
      by_contra! hAll
      exact h (funext hAll)
    rw [if_neg h,Finset.prod_eq_zero (Finset.mem_univ t)]
    simp [ht]

theorem tensor_entries_orthogonal (c : ι → ι → ℝ)
    (hc : ∀ i j, ∑ a, c a i*c a j = if i=j then 1 else 0)
    (m : ℕ) (i j : Fin m → ι) :
    (∑ a : Fin m → ι, (∏ t, c (a t) (i t))*(∏ t, c (a t) (j t))) =
      if i=j then 1 else 0 := by
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun t a => c a (i t)*c a (j t))]
  simp_rw [hc]
  exact prod_kronecker m i j

end

variable {dim : ℕ} [NeZero dim]

@[expose] def frameChange (g : MetricField dim) (y : X dim) (e f : Frame dim) (a i : I dim) : ℝ :=
  frameCoordinatesL g y (e y) (f y a) i

theorem frameChange_reconstruct (g : MetricField dim) (y : X dim) (e f : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (a : I dim) :
    f y a = ∑ i, frameChange g y e f a i • e y i := by
  conv_lhs => rw [← frameVectorL_frameCoordinatesL g y (e y) he (f y a)]
  rw [frameVectorL_apply _ _ y]
  rfl

theorem frameChange_columns_orthogonal (g : MetricField dim) (y : X dim) (e f : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0)
    (hSym : (g y).transpose = g y) (i j : I dim) :
    (∑ a, frameChange g y e f a i * frameChange g y e f a j) = if i=j then 1 else 0 := by
  let u := frameCoordinatesL g y (f y) (e y i)
  let v := frameCoordinatesL g y (f y) (e y j)
  have hEq (a k : I dim) : frameChange g y e f a k = frameChange g y f e k a := by
    simp only [frameChange,frameCoordinatesL_apply,frameCoordinates]
    exact metricPair_symm g y _ _ hSym
  simp_rw [hEq]
  change (∑ a, u a * v a) = _
  have hP : metricPair g y (frameVector f y u) (frameVector f y v) = ∑ a, u a * v a :=
    metricPair_frameVector g f y u v hf
  rw [← hP,← frameVectorL_apply_frame,← frameVectorL_apply_frame]
  change metricPair g y (frameVectorL (f y) (frameCoordinatesL g y (f y) (e y i)))
    (frameVectorL (f y) (frameCoordinatesL g y (f y) (e y j))) = _
  rw [frameVectorL_frameCoordinatesL g y (f y) hf, frameVectorL_frameCoordinatesL g y (f y) hf,he]

theorem jetNorm_eq_of_orthonormalFrames (g : MetricField dim) (y : X dim) (e f : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hf : ∀ i j, metricPair g y (f y i) (f y j) = if i=j then 1 else 0)
    (hSym : (g y).transpose = g y) (u : X dim → ℝ) (m : ℕ) :
    jetNorm g f u m y = jetNorm g e u m y := by
  let c := frameChange g y e f
  let U (a : Fin m → I dim) := ∑ b : Fin m → I dim, covJet g u m y b * ∏ t, e y (a t) (b t)
  let V (a : Fin m → I dim) := ∑ b : Fin m → I dim, covJet g u m y b * ∏ t, f y (a t) (b t)
  have hCoord (a b : I dim) : f y a b = ∑ i, c a i*e y i b := by
    have h := congrArg (EuclideanSpace.proj (𝕜:=ℝ) b) (frameChange_reconstruct g y e f he a)
    simpa only [c,map_sum,map_smul,smul_eq_mul,PiLp.proj_apply] using h
  have hY (a : Fin m → I dim) : V a = ∑ i : Fin m → I dim, (∏ t, c (a t) (i t)) • U i := by
    dsimp only [V,U]
    simp_rw [hCoord,Fintype.prod_sum,Finset.prod_mul_distrib,smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have h := sum_norm_sq_of_orthogonal_matrix (E:=ℝ)
    (fun (a i : Fin m → I dim) => ∏ t, c (a t) (i t))
    (tensor_entries_orthogonal c (frameChange_columns_orthogonal g y e f he hf hSym) m) U
  simp_rw [← hY, Real.norm_eq_abs, sq_abs] at h
  exact congrArg Real.sqrt h

end CalderonN
