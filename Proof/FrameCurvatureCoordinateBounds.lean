import Proof.FrameConnectionCurvature
import Proof.BackgroundCurvature

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres

lemma Elliptic.frameCurvatureCoefficient_physical_bound {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 1 ≤ K) (e : Frame)
    (hFrame : ∀ x ∈ Ω,∀ i j,metricPair g x (e x i) (e x j)=if i=j then 1 else 0)
    {y : X} (hy : y ∈ Ω) (M0 C D : ℝ) (hM0 : 0 ≤ M0) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hEntry : ∀ i j,|g y i j| ≤ M0) (hΓ : ‖connectionBilinear g y‖ ≤ C)
    (hDΓ : ‖fderiv ℝ (connectionBilinear g) y‖ ≤ D) (a b : X) (i j : I) :
    |frameCurvatureCoefficient g e y a b i j| ≤ 18*M0*(D+C^2)*K^2*‖a‖*‖b‖ := by
  have hK0 := zero_lt_one.trans_le hK
  have hE (i : I) : ‖e y i‖ ≤ K := by
    have hSq := hg.frame_norm_sq_bound hK0 e hFrame hy i
    apply (sq_le_sq₀ (norm_nonneg _) hK0.le).mp
    nlinarith only [hSq,hK,sq_nonneg (K-1)]
  have hCurv := metricCurvature_norm_of_operator_bounds g y C D hC hD hΓ hDΓ a b (e y i)
  calc
    _ ≤ 9*M0*‖metricCurvature g y a b (e y i)‖*‖e y j‖ :=
      metricPair_abs_le_of_entry_bound g y M0 hM0 hEntry _ _
    _ ≤ 9*M0*(2*(D+C^2)*‖a‖*‖b‖*‖e y i‖)*‖e y j‖ := by gcongr
    _ ≤ 9*M0*(2*(D+C^2)*‖a‖*‖b‖*K)*K := by gcongr <;> exact hE _
    _ = _ := by ring

/-- Curvature of the actual frame connection has a common bound in fixed
physical base directions, using only finite reference metric budgets. -/
theorem Background.frameConnectionOperator_curvature_coordinate_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    {y : X} (hy : y ∈ Ω) (a b : X) (i j : I) :
    |curvatureLinear (frameConnectionOperator g e) y a b (axis i) j| ≤
      curvatureBudget K |M 0| |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| * ‖a‖*‖b‖ := by
  have hK0 := zero_lt_one.trans_le hK
  rw [h.1.frameConnectionOperator_curvature_coordinate hΩ hK0 e h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2 hy a b i j]
  have hM0 (i j : I) : |g y i j| ≤ |M 0| := (h.reference_entry_bound hy i j).trans (le_abs_self _)
  have hD1 (i j : I) : ‖fderiv ℝ (fun x => g x i j) y‖ ≤ |M ⟨1,by omega⟩| :=
    (h.reference_fderiv_bound (by omega) hy i j).trans (le_abs_self _)
  have hD2 (i j : I) : ‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ |M ⟨2,by omega⟩| :=
    (h.reference_second_fderiv_bound hm hy i j).trans (le_abs_self _)
  have hOps := h.1.connection_operator_bounds hΩ hK0 hy |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
    (abs_nonneg _) (abs_nonneg _) hD1 hD2
  exact h.1.frameCurvatureCoefficient_physical_bound hK e h.2.2.2.2.2.2.2 hy |M 0| _ _
    (abs_nonneg _) (by positivity) (by positivity) hM0 hOps.1 hOps.2 a b i j

end ShrinkingSpheres
