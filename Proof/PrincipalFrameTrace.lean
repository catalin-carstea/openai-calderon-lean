import Proof.MovingFrameSecond
import Proof.MovingTraceDriftField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres

theorem frame_matrix_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (e : Frame) (y : X)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (Q : I → I → E) :
    (∑ i : I,∑ a : I,∑ b : I,(e y i a*e y i b) • Q a b) =
      ∑ a : I,∑ b : I,(g y)⁻¹ a b • Q a b := by
  rw [inverse_metric_of_frame g e y hframe]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,frameMatrix,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem Admissible.frameCovariantTraceSecond_trace {Y Ω : Set X} (hY : IsOpen Y)
    (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ))
    {y : X} (hy : y ∈ Y) {w : X} (hw : w ∈ sphereAt d.γ y) :
    (∑ i : I,frameCovariantTraceSecond d.γ d.adjoint d.frame i i φ (y,w)) =
      ∑ a : I,∑ b : I,(d.γ y)⁻¹ a b • covariantTraceSecond d.γ d.adjoint a b φ (y,w) := by
  simp_rw [hd.frameCovariantTraceSecond_eq hY hSub hK hφ _ _ hy hw]
  exact frame_matrix_contraction d.γ d.frame y (hd.1.2.2.2.2.2.2.2 y (hSub hy)) _

/-- The actual principal operator consists of the orthonormal-frame covariant
    trace and precisely the normalized second-metric tensor from Small. -/
theorem Admissible.principalMovingTrace_frame {Y Ω : Set X} (hY : IsOpen Y)
    (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ))
    {y : X} (hy : y ∈ Y) {w : X} (hw : w ∈ sphereAt d.γ y) :
    principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ (y,w) =
      d.radius y • (∑ i : I,frameCovariantTraceSecond d.γ d.adjoint d.frame i i φ (y,w)) +
      d.radius y • (∑ a : I,∑ b : I,(principal d.γ d.g₂ y-(d.γ y)⁻¹) a b •
        covariantTraceSecond d.γ d.adjoint a b φ (y,w)) := by
  rw [hd.frameCovariantTraceSecond_trace hY hSub hK hφ hy hw]
  have hSplit : (∑ a : I,∑ b : I,principal d.γ d.g₂ y a b •
      covariantTraceSecond d.γ d.adjoint a b φ (y,w)) =
      (∑ a : I,∑ b : I,(d.γ y)⁻¹ a b • covariantTraceSecond d.γ d.adjoint a b φ (y,w)) +
      (∑ a : I,∑ b : I,(principal d.γ d.g₂ y-(d.γ y)⁻¹) a b •
        covariantTraceSecond d.γ d.adjoint a b φ (y,w)) := by
    simp only [Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib]
    abel
  have hModel : principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ (y,w) =
      d.radius y • (∑ a : I,∑ b : I,principal d.γ d.g₂ y a b •
        covariantTraceSecond d.γ d.adjoint a b φ (y,w)) := by
    simp only [principalMovingTrace,covariantTraceSecond,Complex.real_smul]
  rw [hModel,hSplit,smul_add]

end ShrinkingSpheres
