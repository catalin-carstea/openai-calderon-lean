import Proof.ParallelFrameMetricJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def parallelMetricCenterBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (N Z : ℝ) : ℝ :=
  (1+3*(243*K*|M ⟨1,by omega⟩|))*backgroundJointNormalMetricJetBudget hm K M*N^4*Z^2

def parallelMetricAngularBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (N Z : ℝ) : ℝ :=
  backgroundJointNormalMetricJetBudget hm K M*N^4*Z

def parallelMetricMixedBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (N Z : ℝ) : ℝ :=
  (1+4*(243*K*|M ⟨1,by omega⟩|))*backgroundJointNormalMetricJetBudget hm K M*N^4*Z

/-- The SAME actual local parallel-frame metric has uniformly quadratic
    center, angular and mixed jets from the frozen metric budgets. -/
theorem Background.parallel_frame_metric_jet_bounds {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (a : X) (r : ℝ) (hr : 0 ≤ r) (L : X →L[ℝ] X)
    (N Z : ℝ) (hN0 : 0 ≤ N) (hZ : 0 ≤ Z) (hL : ‖L‖ ≤ N) (z : X) (hz : ‖z‖ ≤ Z)
    (hv : metricPair g y (r • L z) (r • L z) < (R y)^2) (hv1 : ‖r • L z‖ ≤ 1) (b : X) (i j : I) :
    |fderiv ℝ (fun p => parallelFrameNormalMetric g E y a r L p i j) (0,z) (1,0)| ≤
      parallelMetricCenterBudget hm K M N Z*r^2*‖a‖ ∧
    |fderiv ℝ (fun p => parallelFrameNormalMetric g E y a r L p i j) (0,z) (0,b)| ≤
      parallelMetricAngularBudget hm K M N Z*r^2*‖b‖ ∧
    |fderiv ℝ (fderiv ℝ (fun p => parallelFrameNormalMetric g E y a r L p i j)) (0,z) (0,b) (1,0)| ≤
      parallelMetricMixedBudget hm K M N Z*r^2*‖a‖*‖b‖ := by
  let Q := backgroundJointNormalMetricJetBudget hm K M
  let C := 243*K*|M ⟨1,by omega⟩|
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hV := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hQ : 0 ≤ Q := by dsimp [Q,backgroundJointNormalMetricJetBudget];positivity
  have hAxis (k : I) : ‖L (axis k)‖ ≤ N := (L.le_opNorm (axis k)).trans
    (by simpa only [norm_axis,mul_one] using hL)
  have hLz : ‖L z‖ ≤ N*Z := (L.le_opNorm z).trans (mul_le_mul hL hz (norm_nonneg _) hN0)
  have hVelocity : ‖r • L z‖ ≤ r*(N*Z) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left hLz hr
  have hAngle : ‖r • L b‖ ≤ r*(N*‖b‖) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left ((L.le_opNorm b).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg b))) hr
  obtain ⟨W,hW,hHere,hTW⟩ := hN.exists_open_metric_tensor_domain hΩ h.1 hy (r • L z) hv.le
  have hT0 := hTW.contDiffAt (hW.mem_nhds hHere)
  constructor
  · rw [fderiv_parallelFrameNormalMetric_center g E y a r L z i j hT0,← Real.norm_eq_abs]
    have hb := h.normal_metric_covariant_center_bound hY hΩ hK hm hN hR hy (r • L z) a (L (axis i)) (L (axis j)) hv hv1
    exact hb.trans ((show (1+3*C)*Q*‖r • L z‖^2*‖a‖*‖L (axis i)‖*‖L (axis j)‖ ≤
      (1+3*C)*Q*(r*(N*Z))^2*‖a‖*N*N by gcongr;exact hAxis i;exact hAxis j).trans_eq
        (by dsimp only [parallelMetricCenterBudget,C,Q];ring))
  constructor
  · rw [fderiv_parallelFrameNormalMetric_vertical g E y a r L z b i j hT0,← Real.norm_eq_abs]
    have hb := (h.reference_normal_metric_vertical_taylor hY hΩ hK hm hN hR hy (r • L z) (L (axis i)) (L (axis j)) hv hv1).2 (r • L b)
    exact hb.trans ((show Q*‖r • L z‖*‖r • L b‖*‖L (axis i)‖*‖L (axis j)‖ ≤
      Q*(r*(N*Z))*(r*(N*‖b‖))*N*N by gcongr;exact hAxis i;exact hAxis j).trans_eq
        (by dsimp only [parallelMetricAngularBudget,Q];ring))
  · rw [fderiv_parallelFrameNormalMetric_mixed g E y a r L z b i j W hW hHere hTW,← Real.norm_eq_abs]
    have hb := h.normal_metric_covariant_center_vertical_derivative_bound hY hΩ hK hm hN hR hy
      (r • L z) a (L (axis i)) (L (axis j)) (r • L b) hv hv1
    exact hb.trans ((show (1+4*C)*Q*‖r • L z‖*‖r • L b‖*‖a‖*‖L (axis i)‖*‖L (axis j)‖ ≤
      (1+4*C)*Q*(r*(N*Z))*(r*(N*‖b‖))*‖a‖*N*N by gcongr;exact hAxis i;exact hAxis j).trans_eq
        (by dsimp only [parallelMetricMixedBudget,C,Q];ring))

end ShrinkingSpheres
