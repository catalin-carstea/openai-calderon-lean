module

public import Proof.CalderonN.Coercivity

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Ring

/-! The frame identities in the released Proposition 5.3's
`Proof/MetricAlgebra.lean`, over the module-enabled definitions. -/

public section

noncomputable section
open Set
open scoped InnerProductSpace
namespace CalderonN

variable {n : ℕ}

lemma metricPair_smul_left (g : MetricField n) (y u v : X n) (a : ℝ) :
    metricPair g y (a • u) v = a * metricPair g y u v := by
  simp only [metricPair, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_smul_right (g : MetricField n) (y u v : X n) (a : ℝ) :
    metricPair g y u (a • v) = a * metricPair g y u v := by
  simp only [metricPair, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_sum_left {α : Type*} (s : Finset α) (g : MetricField n) (y v : X n) (u : α → X n) :
    metricPair g y (∑ a ∈ s, u a) v = ∑ a ∈ s, metricPair g y (u a) v := by
  simp only [metricPair, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

lemma metricPair_sum_right {α : Type*} (s : Finset α) (g : MetricField n) (y u : X n) (v : α → X n) :
    metricPair g y u (∑ a ∈ s, v a) = ∑ a ∈ s, metricPair g y u (v a) := by
  simp only [metricPair, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Reconstruction of a tangent vector from coordinates in the chosen orthonormal frame. -/
@[expose] def frameVector (e : Frame n) (y : X n) (w : X n) : X n := ∑ i, w i • e y i

lemma metricPair_frame_expansion (g : MetricField n) (e : Frame n) (y u v : X n) :
    metricPair g y (frameVector e y u) (frameVector e y v) =
      ∑ i, ∑ j, metricPair g y (e y i) (e y j) * u i * v j := by
  unfold frameVector
  rw [metricPair_sum_left]
  simp_rw [metricPair_smul_left, metricPair_sum_right, metricPair_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_frameVector (γ : MetricField n) (e : Frame n) (y u v : X n)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) :
    metricPair γ y (frameVector e y u) (frameVector e y v) = ∑ i, u i * v i := by
  unfold frameVector
  rw [metricPair_sum_left]
  simp_rw [metricPair_smul_left, metricPair_sum_right, metricPair_smul_right, he]
  simp

lemma frameVector_mem_sphere (γ : MetricField n) (e : Frame n) (y : X n)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (w : ↥(standardSphere n)) : frameVector e y w ∈ sphereAt γ y := by
  change metricPair γ y (frameVector e y w) (frameVector e y w) = 1
  rw [metricPair_frameVector γ e y w w he]
  have hw : ‖w.val‖ = 1 := by simpa only [standardSphere, Metric.mem_sphere, dist_zero_right] using w.property
  simp only [← pow_two, ← EuclideanSpace.real_norm_sq_eq, hw, one_pow]

lemma continuous_frameVector (e : Frame n) (y : X n) : Continuous (frameVector e y) := by
  unfold frameVector
  exact continuous_finsetSum _ fun i _ =>
    (EuclideanSpace.proj i : X n →L[ℝ] ℝ).continuous.smul continuous_const

/-- Coordinates of a tangent vector in a metric-orthonormal frame. -/
@[expose] def frameCoordinates (g : MetricField n) (y : X n) (e : I n → X n) (x : X n) : X n :=
  WithLp.toLp 2 fun i => metricPair g y x (e i)

theorem frameCoordinates_frameVector (g : MetricField n) (y v : X n) (e : I n → X n)
    (he : ∀ i j, metricPair g y (e i) (e j) = if i = j then 1 else 0) :
    frameCoordinates g y e (frameVector (fun _ => e) y v) = v := by
  ext i
  change metricPair g y (∑ j, v j • e j) (e i) = v i
  rw [metricPair_sum_left]
  simp_rw [metricPair_smul_left,he,mul_ite,mul_one,mul_zero]
  simp

/-- The inner products with the columns of a metric-orthonormal frame
are the coordinates of the vector in that frame. -/
theorem frameVector_frameCoordinates (g : MetricField n) (y x : X n)
    (e : I n → X n) (he : ∀ i j, metricPair g y (e i) (e j) = if i = j then 1 else 0) :
    frameVector (fun _ => e) y (frameCoordinates g y e x) = x := by
  let E : Frame n := fun _ => e
  let L : X n →ₗ[ℝ] X n :=
    { toFun := frameVector E y
      map_add' := fun u v => by
        simp only [frameVector,PiLp.add_apply,add_smul,Finset.sum_add_distrib]
      map_smul' := fun a u => by
        simp only [frameVector,PiLp.smul_apply,RingHom.id_apply,Finset.smul_sum,smul_smul,smul_eq_mul] }
  have hzero (v : X n) (hv : L v = 0) : v = 0 := by
    change frameVector E y v = 0 at hv
    have h := metricPair_frameVector g E y v v he
    rw [hv,show metricPair g y 0 0 = 0 by simp [metricPair]] at h
    have hn : ‖v‖ ^ 2 = 0 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa only [pow_two] using h.symm
    rw [pow_two,mul_eq_zero] at hn
    exact norm_eq_zero.mp (hn.elim id id)
  have hinj : Function.Injective L := (LinearMap.ker_eq_bot).mp
    (LinearMap.ker_eq_bot'.mpr hzero)
  obtain ⟨v,hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) x
  change frameVector (fun _ => e) y v = x at hv
  have hcoord : frameCoordinates g y e x = v := by
    rw [← hv,frameCoordinates_frameVector g y v e he]
  rw [hcoord,hv]

theorem inner_frameCoordinates (g : MetricField n) (y x v : X n) (e : I n → X n)
    (he : ∀ i j, metricPair g y (e i) (e j) = if i = j then 1 else 0) :
    ⟪frameCoordinates g y e x, frameCoordinates g y e v⟫_ℝ = metricPair g y x v := by
  have h := metricPair_frameVector g (fun _ => e) y
    (frameCoordinates g y e x) (frameCoordinates g y e v) he
  rw [frameVector_frameCoordinates g y x e he,frameVector_frameCoordinates g y v e he] at h
  rw [h,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem norm_frameCoordinates_sq (g : MetricField n) (y x : X n) (e : I n → X n)
    (he : ∀ i j, metricPair g y (e i) (e j) = if i = j then 1 else 0) :
    ‖frameCoordinates g y e x‖^2 = metricPair g y x x := by
  let v := frameCoordinates g y e x
  have h := metricPair_frameVector g (fun _ => e) y v v he
  rw [frameVector_frameCoordinates g y x e he] at h
  rw [EuclideanSpace.real_norm_sq_eq, h]
  exact Finset.sum_congr rfl fun i _ => pow_two (v i)

end CalderonN
