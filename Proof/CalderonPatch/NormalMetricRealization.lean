module

public import Proof.CalderonPatch.NativeNormalChart

import Proof.CalderonN.MetricPullback
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter Matrix Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis metricPair metricPair_eq_dotProduct coordinateMatrix
  coordinateMatrix_mulVec pullbackMetric vector_eq_sum_axis)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

theorem metricPair_pullbackMetric (g : MetricField n) (F : X n → X n) (x v w : X n) :
    metricPair (pullbackMetric g F) x v w =
      metricPair g (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  let D := fderiv ℝ F x
  let B := coordinateMatrix D
  rw [metricPair_eq_dotProduct, metricPair_eq_dotProduct]
  change (fun i => v i) ⬝ᵥ ((Bᵀ * g (F x) * B) *ᵥ fun i => w i) =
    (fun i => D v i) ⬝ᵥ (g (F x) *ᵥ fun i => D w i)
  rw [← coordinateMatrix_mulVec D v, ← coordinateMatrix_mulVec D w,
    ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose]

/-- The chart coefficients are the native metric in the frame of the
inverse canonical chart, including on the flat boundary face. -/
theorem metricPair_chartMetric (g : SmoothMetric n M) (p : M) (x v w : X n) :
    metricPair (chartMetric g p) x v w =
      let c := extChartAt J p
      let D : X n →L[ℝ] TangentSpace J (c.symm x) := mfderivWithin K J c.symm (range J) x
      g.inner (c.symm x) (D v) (D w) := by
  let c := extChartAt J p
  let D : X n →L[ℝ] TangentSpace J (c.symm x) := mfderivWithin K J c.symm (range J) x
  let b := g.inner (c.symm x)
  have hsum (a : X n) : D a = ∑ i : I n, a i • D (axis i) := by
    conv_lhs => rw [← vector_eq_sum_axis a]
    simp only [map_sum, map_smul]
  change (∑ i, ∑ j, b (D (axis i)) (D (axis j)) * v i * w j) = b (D v) (D w)
  rw [hsum v, hsum w]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem chartMetric_pair_mfderiv (g : SmoothMetric n M) (p x : M)
    (hx : x ∈ (extChartAt J p).source) (v w : TangentSpace J x) :
    let c := extChartAt J p
    metricPair (chartMetric g p) (c x) (mfderiv J K c x v) (mfderiv J K c x w) = g.inner x v w := by
  let c := extChartAt J p
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := J) hx
  have hv := DFunLike.congr_fun h v
  have hw := DFunLike.congr_fun h w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hv hw
  change metricPair (chartMetric g p) (c x) (mfderiv J K c x v) (mfderiv J K c x w) = _
  calc
    _ = g.inner (c.symm (c x))
        ((mfderivWithin K J c.symm (range J) (c x)) (mfderiv J K c x v))
        ((mfderivWithin K J c.symm (range J) (c x)) (mfderiv J K c x w)) :=
      metricPair_chartMetric g p (c x) (mfderiv J K c x v) (mfderiv J K c x w)
    _ = _ := by
      rw [hv, hw]
      exact congrArg (fun q => g.inner q (v : X n) (w : X n)) (c.left_inv hx)

/-- The normalized matrix in the signed chart represents the
specified native metric by the derivative of the actual chart map. -/
theorem normalMetric_represents_native (g : SmoothMetric n M) (p x : M)
    {G : MetricField n} {e : OpenPartialHomeomorph (X n) (X n)}
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hx : x ∈ (extChartAt J p).source) (hy : extChartAt J p x ∈ e.target)
    (hG : G (extChartAt J p x) = chartMetric g p (extChartAt J p x))
    (v w : TangentSpace J x) :
    let a := e.symm ∘ extChartAt J p
    g.inner x v w = metricPair (pullbackMetric G e) (a x) (mfderiv J K a x v) (mfderiv J K a x w) := by
  let c := extChartAt J p
  let a := e.symm ∘ c
  have hMd : MDifferentiableAt K K e.symm (c x) :=
    (hei.contDiffAt (e.open_target.mem_nhds hy)).contMDiffAt.mdifferentiableAt (by simp)
  have hC : MDifferentiableAt J K c x :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hInv : mfderiv K K e.symm (c x) = fderiv ℝ e.symm (c x) := by
    rw [mfderiv_eq_fderiv]
    ext v
    rfl
  have hc := mfderiv_comp x hMd hC
  change mfderiv J K a x = _ at hc
  have hd : (fderiv ℝ e (a x)).comp (fderiv ℝ e.symm (c x)) = ContinuousLinearMap.id ℝ (X n) := by
    have hc := ((he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt
      (by simp)).hasFDerivAt.comp (c x)
      ((hei.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have hId : (e : X n → X n) ∘ e.symm =ᶠ[𝓝 (c x)] id :=
      Filter.mem_of_superset (e.open_target.mem_nhds hy) (fun _ h => e.right_inv h)
    exact (hc.congr_of_eventuallyEq hId.symm).unique (hasFDerivAt_id _)
  let B : TangentSpace J x →L[ℝ] X n := mfderiv J K c x
  let A : TangentSpace J x →L[ℝ] X n := mfderiv J K a x
  let E : X n →L[ℝ] X n := mfderiv K K e.symm (c x)
  have hA' : A = E.comp B := hc
  have hE' : E = fderiv ℝ e.symm (c x) := hInv
  have hv (s : TangentSpace J x) : fderiv ℝ e (a x) (A s) = B s := by
    rw [hA', hE', ContinuousLinearMap.comp_apply]
    exact DFunLike.congr_fun hd (B s)
  change _ = metricPair (pullbackMetric G e) (a x) (A v) (A w)
  rw [metricPair_pullbackMetric, hv v, hv w]
  have hBase : e (a x) = c x := e.right_inv hy
  rw [hBase]
  have hPair : metricPair G (c x) = metricPair (chartMetric g p) (c x) := by
    have hG' : G (c x) = chartMetric g p (c x) := hG
    ext u s
    simp only [metricPair, hG']
  rw [hPair]
  exact (chartMetric_pair_mfderiv g p x hx v w).symm

end CalderonPatch
