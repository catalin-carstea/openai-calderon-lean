module

public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.CarlemanCalculus
public import Proof.CalderonN.FramePullback
public import Proof.CalderonN.MetricConnection
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Star.StarAlgHom

import Proof.CalderonN.MetricPair
import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped InnerProductSpace
open Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The linear map sending frame coordinates to chart coordinates. -/
@[expose] def frameVectorL (e : (I dim) → (X dim)) : (X dim) →L[ℝ] (X dim) :=
  frameVectorLinear (fun _ => e) 0

theorem frameVectorL_apply (e : I dim → X dim) (v y : X dim) :
    frameVectorL e v = frameVector (fun _ => e) y v := by
  simp only [frameVectorL, frameVectorLinear_apply, frameVector]

/-- The linear inverse supplied by a frame orthonormal for the reference metric. -/
@[expose] def frameCoordinatesL (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim)) : (X dim) →L[ℝ] (X dim) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : (I dim) => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (metricBilinear γ y).flip (e i))

theorem frameCoordinatesL_apply (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim)) (v : (X dim)) :
    frameCoordinatesL γ y e v = frameCoordinates γ y e v := by
  ext i
  change metricBilinear γ y v (e i) = metricPair γ y v (e i)
  exact metricBilinear_apply γ y v (e i)

theorem frameCoordinatesL_frameVectorL (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0) (v : (X dim)) :
    frameCoordinatesL γ y e (frameVectorL e v) = v := by
  rw [frameCoordinatesL_apply,frameVectorL_apply e v y,frameCoordinates_frameVector _ _ _ _ he]

theorem frameVectorL_frameCoordinatesL (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0) (v : (X dim)) :
    frameVectorL e (frameCoordinatesL γ y e v) = v := by
  rw [frameVectorL_apply _ _ y,frameCoordinatesL_apply,frameVector_frameCoordinates _ _ _ _ he]

private theorem frameVectorL_comp_frameCoordinatesL (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0) :
    (frameVectorL e).comp (frameCoordinatesL γ y e) = ContinuousLinearMap.id ℝ (X dim) := by
  ext v : 1
  exact frameVectorL_frameCoordinatesL γ y e he v

@[expose] def frameMetricOperator (M : (Mat dim)) (e : (I dim) → (X dim)) : (X dim) →L[ℝ] (X dim) :=
  (frameVectorL e).adjoint.comp ((Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M).comp (frameVectorL e))

@[expose] def frameCometricOperator (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim)) (P : (Mat dim)) : (X dim) →L[ℝ] (X dim) :=
  (frameCoordinatesL γ y e).comp ((Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) P).comp (frameCoordinatesL γ y e).adjoint)

theorem inner_frameMetricOperator (g : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim)) (v w : (X dim)) :
    ⟪v,frameMetricOperator (g y) e w⟫_ℝ = metricPair g y (frameVectorL e v) (frameVectorL e w) := by
  rw [frameMetricOperator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply,Matrix.inner_toEuclideanCLM,metricPair_eq_dotProduct]

theorem frameCometricOperator_frameMetricOperator
    (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0)
    (M : (Mat dim)) (hM : M.PosDef) (v : (X dim)) :
    frameCometricOperator γ y e M⁻¹ (frameMetricOperator M e v) = v := by
  let S := frameCoordinatesL γ y e
  let F := frameVectorL e
  have hAdj : S.adjoint.comp F.adjoint = ContinuousLinearMap.id ℝ (X dim) := by
    rw [← ContinuousLinearMap.adjoint_comp,frameVectorL_comp_frameCoordinatesL _ _ _ he,
      ContinuousLinearMap.adjoint_id]
  have hM' (w : (X dim)) : Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M⁻¹ (Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M w) = w := by
    change (Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M⁻¹ * Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M : (X dim) →L[ℝ] (X dim)) w = w
    rw [← map_mul,Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM.det_pos.ne'),map_one]
    rfl
  change S (Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M⁻¹ (S.adjoint
    (F.adjoint (Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M (F v))))) = v
  rw [show ∀ z, S.adjoint (F.adjoint z) = z from fun z =>
        DFunLike.congr_fun hAdj z,hM']
  exact frameCoordinatesL_frameVectorL γ y e he v

theorem frameMetricOperator_ref_eq_id (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0) :
    frameMetricOperator (γ y) e = ContinuousLinearMap.id ℝ (X dim) := by
  ext w : 1
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.id_apply,inner_frameMetricOperator,
    frameVectorL_apply e v y,frameVectorL_apply e w y,metricPair_frameVector _ _ _ _ _ he,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem frameCometricOperator_ref_eq_id (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0)
    (hγ : (γ y).PosDef) :
    frameCometricOperator γ y e (γ y)⁻¹ = ContinuousLinearMap.id ℝ (X dim) := by
  ext v : 1
  have h := frameCometricOperator_frameMetricOperator γ y e he (γ y) hγ v
  rwa [frameMetricOperator_ref_eq_id _ _ _ he] at h

theorem norm_le_dim_mul_of_abs_coord_le {z : (X dim)} {a : ℝ} (ha : 0 ≤ a)
    (hz : ∀ i, |z i| ≤ a) : ‖z‖ ≤ (dim : ℝ)*a := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have hs (i : (I dim)) : (z i)^2 ≤ a^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).mpr (hz i)
  calc
    (∑ i : (I dim), (z i)^2) ≤ ∑ _i : (I dim), a^2 := Finset.sum_le_sum fun i _ => hs i
    _ ≤ ((dim : ℝ)*a)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn : (1 : ℝ) ≤ dim := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne dim)
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by nlinarith only [hn, sq_nonneg ((dim : ℝ)-1)]) (sq_nonneg a)

theorem norm_toEuclideanCLM_le_of_entries (M : (Mat dim)) {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ i j, |M i j| ≤ a) :
    ‖(Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M : (X dim) →L[ℝ] (X dim))‖ ≤ (dim : ℝ)^2*a := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have h (i : (I dim)) : |(Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) M v : (X dim)) i| ≤ (dim : ℝ)*a*‖v‖ := by
    rw [Matrix.ofLp_toEuclideanCLM]
    change |∑ j, M i j * v j| ≤ _
    calc
      _ ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : (I dim), a * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        have hj : |v j| ≤ ‖v‖ := by
          rw [← Real.norm_eq_abs]
          exact PiLp.norm_apply_le v j
        exact mul_le_mul (hM i j) hj (abs_nonneg _) ha
      _ = _ := by simp [I]; ring
  exact (norm_le_dim_mul_of_abs_coord_le (by positivity) h).trans_eq (by ring)

theorem norm_frameCometricOperator_sub_id_le
    (γ : (MetricField dim)) (y : (X dim)) (e : (I dim) → (X dim))
    (he : ∀ i j, metricPair γ y (e i) (e j) = if i = j then 1 else 0)
    (hγ : (γ y).PosDef) {K : ℝ} (hK : 0 ≤ K)
    (hell : ∀ v, metricPair γ y v v ≤ K * ‖v‖^2) (P : (Mat dim)) :
    ‖frameCometricOperator γ y e P - ContinuousLinearMap.id ℝ (X dim)‖ ≤
      K * ‖(Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) (P - (γ y)⁻¹) : (X dim) →L[ℝ] (X dim))‖ := by
  let S := frameCoordinatesL γ y e
  let A : (X dim) →L[ℝ] (X dim) := Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ) (P - (γ y)⁻¹)
  have hS : ‖S‖ ≤ Real.sqrt K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [show S v = frameCoordinates γ y e v from frameCoordinatesL_apply γ y e v,
      norm_frameCoordinates_sq _ _ _ _ he,mul_pow,Real.sq_sqrt hK]
    exact hell v
  have hEq : frameCometricOperator γ y e P - ContinuousLinearMap.id ℝ (X dim) =
      S.comp (A.comp S.adjoint) := by
    rw [← frameCometricOperator_ref_eq_id _ _ _ he hγ]
    ext v : 1
    simp [frameCometricOperator,S,A,map_sub]
  rw [hEq]
  calc
    ‖S.comp (A.comp S.adjoint)‖ ≤ ‖S‖ * ‖A.comp S.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖S‖ * (‖A‖ * ‖S.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ Real.sqrt K * (‖A‖ * Real.sqrt K) := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
    _ = K * ‖A‖ := by
      rw [show Real.sqrt K * (‖A‖ * Real.sqrt K) = (Real.sqrt K)^2 * ‖A‖ by ring,
        Real.sq_sqrt hK]

end CalderonN
