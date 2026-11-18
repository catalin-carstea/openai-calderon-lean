import Proof.FrameCoordinateCovectors
import Proof.PrincipalFrameTrace
import Proof.MetricSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

def frameTensorMatrix (g : MetricField) (e : Frame) (y : X) (Q : Mat) : Mat :=
  fun i j => ∑ a : I,∑ b : I,Q a b*frameCoordinateLinear g e y i (axis a)*frameCoordinateLinear g e y j (axis b)

lemma frameTensorMatrix_reconstruct (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0) (Q : Mat) (a b : I) :
    (∑ i : I,∑ j : I,frameTensorMatrix g e y Q i j*e y i a*e y j b)=Q a b := by
  have hDual (c a : I) : (∑ i : I,frameCoordinateLinear g e y i (axis c)*e y i a)=(axis c) a := by
    have hh := congrArg (fun v : X => v a) (frameCoordinateLinear_reconstruct g e y (axis c) he)
    simpa only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul] using hh
  calc
    _ = ∑ c : I,∑ d : I,Q c d*(∑ i : I,frameCoordinateLinear g e y i (axis c)*e y i a)*
        (∑ j : I,frameCoordinateLinear g e y j (axis d)*e y j b) := by
      simp only [frameTensorMatrix,Fin.sum_univ_three]
      ring
    _ = ∑ c : I,∑ d : I,Q c d*(axis c a)*(axis d b) := by simp only [hDual]
    _ = Q a b := by simp [axis,PiLp.single_apply]

/-- Actual coframe contraction of a coordinate tensor, with no derivative of
    the arbitrary orthonormal frame. -/
theorem frameTensorMatrix_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (Q : Mat) (T : I → I → E) :
    (∑ a : I,∑ b : I,Q a b • T a b)=
      ∑ i : I,∑ j : I,frameTensorMatrix g e y Q i j •
        (∑ a : I,∑ b : I,(e y i a*e y j b) • T a b) := by
  calc
    _ = ∑ a : I,∑ b : I,(∑ i : I,∑ j : I,frameTensorMatrix g e y Q i j*e y i a*e y j b) • T a b := by
      simp only [frameTensorMatrix_reconstruct g e y he]
    _ = _ := by
      simp only [Fin.sum_univ_three]
      module

lemma frameTensorMatrix_inverse_metric (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0) (i j : I) :
    frameTensorMatrix g e y (g y)⁻¹ i j=if i=j then 1 else 0 := by
  have hExpand (k l : I) := linear_axis_expansion (frameCoordinateLinear g e y k) (e y l)
  calc
    _ = ∑ k : I,(∑ a : I,e y k a*frameCoordinateLinear g e y i (axis a))*
        (∑ b : I,e y k b*frameCoordinateLinear g e y j (axis b)) := by
      rw [show (g y)⁻¹=frameMatrix e y*(frameMatrix e y).transpose from inverse_metric_of_frame g e y he]
      simp only [frameTensorMatrix,Matrix.mul_apply,Matrix.transpose_apply,frameMatrix,Fin.sum_univ_three]
      ring
    _ = ∑ k : I,frameCoordinateLinear g e y i (e y k)*frameCoordinateLinear g e y j (e y k) := by
      simp only [← hExpand]
    _ = _ := by simp [frameCoordinateLinear_apply,he,eq_comm]

lemma frameTensorMatrix_sub (g : MetricField) (e : Frame) (y : X) (Q R : Mat) (i j : I) :
    frameTensorMatrix g e y (Q-R) i j=frameTensorMatrix g e y Q i j-frameTensorMatrix g e y R i j := by
  simp only [frameTensorMatrix,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]

lemma frameTensorMatrix_symmetric (g : MetricField) (e : Frame) (y : X) (Q : Mat)
    (hQ : ∀ a b,Q a b=Q b a) (i j : I) :
    frameTensorMatrix g e y Q i j=frameTensorMatrix g e y Q j i := by
  rw [frameTensorMatrix,frameTensorMatrix,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hQ a b]
  ring

lemma frameTensorMatrix_abs_le {Ω : Set X} (g : MetricField) (e : Frame) {K : ℝ}
    (h : Elliptic Ω K g) (hK : 1 ≤ K) {y : X} (hy : y ∈ Ω)
    (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (Q : Mat) {B : ℝ} (hB : 0 ≤ B) (hQ : ∀ a b,|Q a b| ≤ B) (i j : I) :
    |frameTensorMatrix g e y Q i j| ≤ 9*B*K^2 := by
  have hK0 := zero_le_one.trans hK
  have hc (i a : I) : |frameCoordinateLinear g e y i (axis a)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact h.frame_coordinate_abs_bound hK e hy he a i
  have hTerm (a b : I) : |Q a b*frameCoordinateLinear g e y i (axis a)*frameCoordinateLinear g e y j (axis b)| ≤ B*K*K := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hQ a b) (hc i a) (abs_nonneg _) hB) (hc j b) (abs_nonneg _) (mul_nonneg hB hK0)
  calc
    _ ≤ ∑ a : I,∑ b : I,|Q a b*frameCoordinateLinear g e y i (axis a)*frameCoordinateLinear g e y j (axis b)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _a : I,∑ _b : I,B*K*K := Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hTerm a b))
    _ = _ := by simp only [Fin.sum_univ_three];ring

lemma contDiffOn_frameTensorMatrix {Y : Set X} (g : MetricField) (e : Frame) {K : ℝ}
    (h : Elliptic Y K g) (he : ∀ j,ContDiffOn ℝ ∞ (fun x => e x j) Y)
    (Q : MetricField) (hQ : ∀ a b,ContDiffOn ℝ ∞ (fun x => Q x a b) Y) (i j : I) :
    ContDiffOn ℝ ∞ (fun x => frameTensorMatrix g e x (Q x) i j) Y := by
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  have hCi := h.contDiffOn_metricPair (fun _ => axis a) (fun x => e x i) contDiffOn_const (he i)
  have hCj := h.contDiffOn_metricPair (fun _ => axis b) (fun x => e x j) contDiffOn_const (he j)
  simpa only [frameCoordinateLinear_apply] using ((hQ a b).mul hCi).mul hCj

lemma Admissible.principalMovingTrace_frame_matrix {Y Ω : Set X} (hY : IsOpen Y)
    (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y)
    {w : X} (hw : w ∈ sphereAt d.γ y) :
    principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ (y,w)=
      d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
        frameCovariantTraceSecond d.γ d.adjoint d.frame i j φ (y,w)) := by
  have hModel : principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ (y,w)=
      d.radius y • (∑ a : I,∑ b : I,principal d.γ d.g₂ y a b • covariantTraceSecond d.γ d.adjoint a b φ (y,w)) := by
    simp only [principalMovingTrace,covariantTraceSecond,Complex.real_smul]
  rw [hModel,frameTensorMatrix_contraction d.γ d.frame y (hd.1.2.2.2.2.2.2.2 y (hSub hy))]
  apply congrArg (fun v : ℂ => d.radius y • v)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v : ℂ => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j • v)
    (hd.frameCovariantTraceSecond_eq hY hSub hK hφ i j hy hw).symm
end ShrinkingSpheres
