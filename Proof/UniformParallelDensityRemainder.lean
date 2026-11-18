import Proof.NormalizedDensityNeighborhood

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def parallelDensityValueBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (N Z : ℝ) : ℝ :=
  backgroundNormalizedDensityJetBudget hm K M*N^2*Z^2

def parallelDensityAngularBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (N Z : ℝ) : ℝ :=
  backgroundNormalizedDensityJetBudget hm K M*N^2*Z

def parallelDensityCenterBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (N Z : ℝ) : ℝ :=
  (1+243*K*|M ⟨1,by omega⟩|)*parallelDensityValueBudget hm K M N Z

def parallelDensityMixedBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (N Z : ℝ) : ℝ :=
  (1+2*(243*K*|M ⟨1,by omega⟩|))*parallelDensityAngularBudget hm K M N Z

/-- Value, angular, center and mixed estimates for the same actual normalized
    scalar family after subtracting its canonical affine first model. -/
theorem Background.parallel_density_remainder_jet_bounds {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (a : X) (r : ℝ) (hr : 0 ≤ r) (L : X →L[ℝ] X)
    (N Z : ℝ) (hN0 : 0 ≤ N) (hZ : 0 ≤ Z) (hL : ‖L‖ ≤ N) (z : X) (hz : ‖z‖ ≤ Z)
    (hv : metricPair g y (r • L z) (r • L z) < (R y)^2) (hv1 : ‖r • L z‖ ≤ 1) (b : X) :
    let F := parallelNormalizedDensityRemainder g g₁ E y a r L
    |F (0,z)| ≤ parallelDensityValueBudget hm K M N Z*r^2 ∧
    |fderiv ℝ F (0,z) (0,b)| ≤ parallelDensityAngularBudget hm K M N Z*r^2*‖b‖ ∧
    |fderiv ℝ F (0,z) (1,0)| ≤ parallelDensityCenterBudget hm K M N Z*r^2*‖a‖ ∧
    |fderiv ℝ (fderiv ℝ F) (0,z) (0,b) (1,0)| ≤ parallelDensityMixedBudget hm K M N Z*r^2*‖a‖*‖b‖ := by
  dsimp only
  let Q := backgroundNormalizedDensityJetBudget hm K M
  let C := 243*K*|M ⟨1,by omega⟩|
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hV := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hQ : 0 ≤ Q := by dsimp [Q,backgroundNormalizedDensityJetBudget];positivity
  have hLz : ‖L z‖ ≤ N*Z := (L.le_opNorm z).trans (mul_le_mul hL hz (norm_nonneg _) hN0)
  have hVelocity : ‖r • L z‖ ≤ r*(N*Z) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hLz hr
  have hAngle : ‖r • L b‖ ≤ r*(N*‖b‖) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((L.le_opNorm b).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg b))) hr
  have hF := (h.normalized_joint_first_density_jets hY hΩ hK hm hN hR hy (r • L z) hv hv1).1
  have hEll := (h.firstDensityLogDifferential_smooth hK hΩ).contDiffAt (hΩ.mem_nhds (hN.center_mem hy))
  have hTaylor := h.normalized_joint_density_affine_taylor hY hΩ hK hm hN hR hy (r • L z) hv hv1
  refine ⟨?_,?_,?_,?_⟩
  · simp only [parallelNormalizedDensityRemainder,normalizedDensityAffineRemainder,
      parallelFrameInput,zero_smul,add_zero,affineParallelFrame_zero]
    rw [← Real.norm_eq_abs]
    exact hTaylor.1.trans ((show Q*‖r • L z‖^2 ≤ Q*(r*(N*Z))^2 by gcongr).trans_eq
      (by dsimp only [parallelDensityValueBudget,Q];ring))
  · rw [fderiv_parallelNormalizedDensityRemainder_vertical g g₁ E y a r L z b hF hEll,← Real.norm_eq_abs]
    exact (hTaylor.2.1 (r • L b)).trans ((show Q*‖r • L z‖*‖r • L b‖ ≤ Q*(r*(N*Z))*(r*(N*‖b‖)) by gcongr).trans_eq
      (by dsimp only [parallelDensityAngularBudget,Q];ring))
  · rw [fderiv_parallelNormalizedDensityRemainder_center g g₁ E y a r L z hF hEll,← Real.norm_eq_abs]
    have hb := h.normalized_density_covariant_center_bound hY hΩ hK hm hN hR hy (r • L z) a hv hv1
    exact hb.trans ((show (1+C)*Q*‖r • L z‖^2*‖a‖ ≤ (1+C)*Q*(r*(N*Z))^2*‖a‖ by gcongr).trans_eq
      (by dsimp only [parallelDensityCenterBudget,parallelDensityValueBudget,C,Q];ring))
  · obtain ⟨W,hW,hp,hFW⟩ := h.exists_open_normalized_density_domain hΩ hK hN hy (r • L z) hv.le
    rw [fderiv_parallelNormalizedDensityRemainder_mixed g g₁ E y a r L z b W hW hp hFW hEll,← Real.norm_eq_abs]
    have hb := h.normalized_density_covariant_center_vertical_derivative_bound hY hΩ hK hm hN hR hy
      (r • L z) a (r • L b) hv hv1
    exact hb.trans ((show (1+2*C)*Q*‖r • L z‖*‖r • L b‖*‖a‖ ≤
      (1+2*C)*Q*(r*(N*Z))*(r*(N*‖b‖))*‖a‖ by gcongr).trans_eq
        (by dsimp only [parallelDensityMixedBudget,parallelDensityAngularBudget,C,Q];ring))

end ShrinkingSpheres
