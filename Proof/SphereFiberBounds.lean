import Proof.SphereSobolevPhysicalPair
import Proof.SmoothBoundarySeparation
import Proof.EnergyPositivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

theorem smoothNear.continuous_frame_fiber {Y : Set X} {g : MetricField} {F : Field}
    (hF : smoothNear F (bundle Y g)) {y : X} (hy : y ∈ Y) (e : Frame)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) :
    Continuous (fun w : UnitSphere => F (y,frameVector e y w.val)) := by
  exact (hF.sphere_slice hy).continuous_frame_slice hframe

theorem norm_fin_three_sum_sq_le {E : Type*} [SeminormedAddCommGroup E] (F : I → E) :
    ‖∑ i : I,F i‖^2 ≤ 3*∑ i : I,‖F i‖^2 := by
  have h := norm_sum_le Finset.univ F
  have hSum : 0 ≤ ∑ i : I,‖F i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs := (sq_le_sq₀ (norm_nonneg _) hSum).mpr h
  simp only [Fin.sum_univ_three] at hs ⊢
  nlinarith only [hs,sq_nonneg (‖F 0‖-‖F 1‖),sq_nonneg (‖F 0‖-‖F 2‖),sq_nonneg (‖F 1‖-‖F 2‖)]

theorem fiberSq_sum_three_le (e : Frame) (y : X) (F : I → X → ℂ)
    (hF : ∀ i,Continuous (fun w : UnitSphere => F i (frameVector e y w.val))) :
    fiberSq e y (fun w => ∑ i : I,F i w) ≤ 3*∑ i : I,fiberSq e y (F i) := by
  have hEach (i : I) : Integrable (fun w : UnitSphere => ‖F i (frameVector e y w.val)‖^2) sphereProbability :=
    ((hF i).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSumCont : Continuous (fun w : UnitSphere => ∑ i : I,F i (frameVector e y w.val)) :=
    continuous_finsetSum _ (fun i _ => hF i)
  have hInt : Integrable (fun w : UnitSphere => ‖∑ i : I,F i (frameVector e y w.val)‖^2) sphereProbability :=
    (hSumCont.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hBound : Integrable (fun w : UnitSphere => 3*∑ i : I,‖F i (frameVector e y w.val)‖^2) sphereProbability :=
    (integrable_finsetSum _ (fun i _ => hEach i)).const_mul 3
  rw [fiberSq_integral_norm]
  apply (integral_mono hInt hBound (fun w => norm_fin_three_sum_sq_le _)).trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => hEach i)]
  simp only [fiberSq_integral_norm]

theorem fiberSq_real_weight_sum_three_le (e : Frame) (y : X) (F : I → X → ℂ)
    (hF : ∀ i,Continuous (fun w : UnitSphere => F i (frameVector e y w.val)))
    (c : I → ℝ) (K : ℝ) (hK : 0 ≤ K) (hc : ∀ i,|c i| ≤ K) :
    fiberSq e y (fun w => ∑ i : I,c i • F i w) ≤ 3*K^2*∑ i : I,fiberSq e y (F i) := by
  have h := fiberSq_sum_three_le e y (fun i w => c i • F i w) (fun i => (hF i).const_smul (c i))
  simp only [fiberSq_smul_real] at h
  have hEach (i : I) : (c i)^2*fiberSq e y (F i) ≤ K^2*fiberSq e y (F i) := by
    have hs : (c i)^2 ≤ K^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hc i)
    exact mul_le_mul_of_nonneg_right hs (fiberSq_nonneg e y (F i))
  exact h.trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hEach i)) (by norm_num : (0:ℝ) ≤ 3)).trans_eq
    (by rw [← Finset.mul_sum];ring))

end ShrinkingSpheres
