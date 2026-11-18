import Proof.SphereFiberBounds
import Proof.HessianCoordinateBounds
import Proof.PhysicalTraceRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def horizontalBaseL (g : MetricField) (F : Field) (y w : X) : X →L[ℝ] ℂ :=
  (fderiv ℝ F (y,w)).comp ((ContinuousLinearMap.id ℝ X).prod (-(connectionBilinear g y).flip w))

theorem horizontalBaseL_apply (g : MetricField) (F : Field) (y w a : X) :
    horizontalBaseL g F y w a = horizontal g F y w a := by
  simp only [horizontalBaseL,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,_root_.neg_apply,ContinuousLinearMap.flip_apply,connectionBilinear_apply]
  rfl

theorem horizontal_frame_expansion (g : MetricField) (e : Frame) (F : Field) (y w a : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) :
    horizontal g F y w a = ∑ j : I,frameCoordinateLinear g e y j a • horizontal g F y w (e y j) := by
  have h := congrArg (horizontalBaseL g F y w) (frameCoordinateLinear_reconstruct g e y a hframe)
  rw [map_sum] at h
  simpa only [map_smul,horizontalBaseL_apply] using h.symm

theorem fiberSq_add_le (e : Frame) (y : X) (F G : X → ℂ)
    (hF : Continuous (fun w : UnitSphere => F (frameVector e y w.val)))
    (hG : Continuous (fun w : UnitSphere => G (frameVector e y w.val))) :
    fiberSq e y (fun w => F w+G w) ≤ 2*fiberSq e y F+2*fiberSq e y G := by
  have hFi : Integrable (fun w : UnitSphere => ‖F (frameVector e y w.val)‖^2) sphereProbability :=
    (hF.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGi : Integrable (fun w : UnitSphere => ‖G (frameVector e y w.val)‖^2) sphereProbability :=
    (hG.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSum : Integrable (fun w : UnitSphere => ‖F (frameVector e y w.val)+G (frameVector e y w.val)‖^2) sphereProbability :=
    ((hF.add hG).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (a b : ℂ) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
    have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr (norm_add_le a b)
    nlinarith only [hn,sq_nonneg (‖a‖-‖b‖)]
  rw [fiberSq_integral_norm,fiberSq_integral_norm,fiberSq_integral_norm]
  apply (integral_mono hSum ((hFi.const_mul 2).add (hGi.const_mul 2)) (fun w => hPoint _ _)).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add (hFi.const_mul 2) (hGi.const_mul 2),integral_const_mul,integral_const_mul]

/-- Coordinate horizontal derivatives are controlled by orthonormal-frame
    derivatives using only ellipticity and frame values. -/
theorem horizontal_coordinate_fiber_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => e x j) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    {F : Field} (hF : smoothNear F (bundle Y g)) {y : X} (hy : y ∈ Y) (i : I) :
    fiberSq e y (fun w => horizontal g F y w (axis i)) ≤
      3*K^2*∑ j : I,fiberSq e y (fun w => horizontal g F y w (e y j)) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCont (j : I) : Continuous (fun w : UnitSphere => horizontal g F y (frameVector e y w.val) (e y j)) :=
    (smoothNear_horizontalField hY h hKpos e he hF j).continuous_frame_fiber hy e (hframe y hy)
  have hCoeff (j : I) : |frameCoordinateLinear g e y j (axis i)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact h.frame_coordinate_abs_bound hK e hy (hframe y hy) i j
  have hEq : fiberSq e y (fun w => horizontal g F y w (axis i)) =
      fiberSq e y (fun w => ∑ j : I,frameCoordinateLinear g e y j (axis i) • horizontal g F y w (e y j)) := by
    apply fiberSq_congr_frameVector
    intro w
    exact horizontal_frame_expansion g e F y _ (axis i) (hframe y hy)
  rw [hEq]
  exact fiberSq_real_weight_sum_three_le e y _ hCont _ K (zero_le_one.trans hK) hCoeff

theorem horizontal_coordinate_fiber_sum_bound {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 1 ≤ K) (e : Frame)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => e x j) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    {F : Field} (hF : smoothNear F (bundle Y g)) {y : X} (hy : y ∈ Y) :
    (∑ i : I,fiberSq e y (fun w => horizontal g F y w (axis i))) ≤
      9*K^2*∑ j : I,fiberSq e y (fun w => horizontal g F y w (e y j)) := by
  have hEach := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => horizontal_coordinate_fiber_bound hY h hK e he hframe hF hy i)
  exact hEach.trans_eq (by rw [Fin.sum_univ_three];ring)

end ShrinkingSpheres
