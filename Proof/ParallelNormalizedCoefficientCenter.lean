import Proof.UniformParallelDensityRemainder
import Proof.ParallelScalarBounds
import Proof.QuadraticProductRemainder
import Proof.ParallelFirstMetricCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Operator
namespace ShrinkingSpheres

def parallelNormalizedCoefficientCenterBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ)
    (N Z H0 HC : ℝ) : ℝ :=
  |parallelDensityCenterBudget hm K M N Z|+
    backgroundNormalizedDensityJetBudget hm K M*(1+243*K*|M ⟨1,by omega⟩|)*H0+
    backgroundNormalizedDensityJetBudget hm K M*HC

def parallelNormalizedCoefficientMixedBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ)
    (N Z H0 HC HZ HM : ℝ) : ℝ :=
  |parallelDensityMixedBudget hm K M N Z|+
    backgroundNormalizedDensityJetBudget hm K M*(1+2*(243*K*|M ⟨1,by omega⟩|))*N*H0+
    backgroundNormalizedDensityJetBudget hm K M*(1+243*K*|M ⟨1,by omega⟩|)*HZ+
    backgroundNormalizedDensityJetBudget hm K M*N*HC+backgroundNormalizedDensityJetBudget hm K M*HM

/-- The scalar and reference-coefficient producers control the SAME actual
    normalized first-metric coefficient and its canonical first-model remainder. -/
theorem Background.parallel_normalized_coefficient_center_bounds {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (a : X) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (L : X →L[ℝ] X)
    (N Z : ℝ) (hN0 : 0 ≤ N) (hZ : 0 ≤ Z) (hL : ‖L‖ ≤ N) (z : X) (hz : ‖z‖ ≤ Z)
    (hv : metricPair g y (r • L z) (r • L z) < (R y)^2) (hv1 : ‖r • L z‖ ≤ 1) (b : X) (i j : I)
    (hPos : 0 < (parallelFrameNormalMetric g E y a r L (0,z)).det)
    (H0 HC HZ HM : ℝ) (hH0 : 0 ≤ H0) (hHC : 0 ≤ HC) (hHZ : 0 ≤ HZ) (hHM : 0 ≤ HM)
    (hHv : |matrixFamilyCoefficient (parallelFrameNormalMetric g E y a r L) (0,z) i j-(1:Mat) i j| ≤ H0*r^2)
    (hHc : |fderiv ℝ (fun p => matrixFamilyCoefficient (parallelFrameNormalMetric g E y a r L) p i j) (0,z) (1,0)| ≤ HC*r^2*‖a‖)
    (hHz : |fderiv ℝ (fun p => matrixFamilyCoefficient (parallelFrameNormalMetric g E y a r L) p i j) (0,z) (0,b)| ≤ HZ*r^2*‖b‖)
    (hHm : |fderiv ℝ (fderiv ℝ (fun p => matrixFamilyCoefficient (parallelFrameNormalMetric g E y a r L) p i j)) (0,z) (0,b) (1,0)| ≤ HM*r^2*‖a‖*‖b‖) :
    |fderiv ℝ (fun p => parallelNormalizedFirstCoefficientRemainder g g₁ E y a r L p i j) (0,z) (1,0)| ≤
      parallelNormalizedCoefficientCenterBudget hm K M N Z H0 HC*r^2*‖a‖ ∧
    |fderiv ℝ (fderiv ℝ (fun p => parallelNormalizedFirstCoefficientRemainder g g₁ E y a r L p i j)) (0,z) (0,b) (1,0)| ≤
      parallelNormalizedCoefficientMixedBudget hm K M N Z H0 HC HZ HM*r^2*‖a‖*‖b‖ := by
  let Q := backgroundNormalizedDensityJetBudget hm K M
  let C := 243*K*|M ⟨1,by omega⟩|
  let G := parallelFrameNormalMetric g E y a r L
  let F := normalizedJointFirstDensityFactor g g₁ E
  let S0 := parallelNormalizedDensity g g₁ E y a r L
  let R0 := parallelNormalizedDensityRemainder g g₁ E y a r L
  let H := fun p => matrixFamilyCoefficient G p i j
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hV := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hQ : 0 ≤ Q := by dsimp [Q,backgroundNormalizedDensityJetBudget];positivity
  obtain ⟨W,hW,hp,hFW⟩ := h.exists_open_normalized_density_domain hΩ hK hN hy (r • L z) hv.le
  have hJets := h.normalized_joint_first_density_jets hY hΩ hK hm hN hR hy (r • L z) hv hv1
  have hFirst : ‖fderiv ℝ F (y,r • L z)‖ ≤ Q := by
    have hb := hJets.2 1 (by omega);rwa [norm_iteratedFDeriv_one] at hb
  have hSecond : ‖fderiv ℝ (fderiv ℝ F) (y,r • L z)‖ ≤ Q := by
    have hb := hJets.2 2 (by omega);rwa [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hb
  have hNv : |S0 (0,z)| ≤ Q := by
    have hb := hJets.2 0 (by omega)
    simpa only [S0,parallelNormalizedDensity,parallelFrameInput,affineParallelFrame_zero,zero_smul,add_zero,
      norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb
  have hScalar := parallelScalar_directional_bounds F g y a r L z b W hW hp hFW Q C N hQ hC hN0 hr hr1
    hv1 hL (h.connection_budget hK (by omega) (hN.center_mem hy)) hFirst hSecond
  have hRem := h.parallel_density_remainder_jet_bounds hY hΩ hK hm hN hR hy a r hr L N Z hN0 hZ hL z hz hv hv1 b
  have hEll := (h.firstDensityLogDifferential_smooth hK hΩ).contDiffAt (hΩ.mem_nhds (hN.center_mem hy))
  have hAt : ContDiffAt ℝ ∞ F (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,affineParallelFrame_zero,zero_smul,add_zero] using hJets.1
  have hS0 : ContDiffAt ℝ ∞ S0 (0,z) := hAt.comp (0,z) (contDiff_parallelFrameInput g y a r L).contDiffAt
  have hRAt := contDiffAt_normalizedDensityAffineRemainder g g₁ E y (r • L z) hJets.1 hEll
  have hRInput : ContDiffAt ℝ ∞ (normalizedDensityAffineRemainder g g₁ E) (parallelFrameInput g y a r L (0,z)) := by
    simpa only [parallelFrameInput,affineParallelFrame_zero,zero_smul,add_zero] using hRAt
  have hR0 : ContDiffAt ℝ ∞ R0 (0,z) := hRInput.comp (0,z) (contDiff_parallelFrameInput g y a r L).contDiffAt
  obtain ⟨S,hS,hHere,hGS,hDet⟩ := hN.exists_parallel_frame_metric_domain hΩ h.1 hy a r L z hv.le hPos
  have hNe (p) (hp : p ∈ S) : (G p).det ≠ 0 := (hDet p hp).ne'
  have hHS : ContDiffOn ℝ ∞ H S := (contDiffOn_matrixFamily_density G hGS hNe).mul
    (contDiffOn_matrixFamily_inverse_entry G hGS hNe i j)
  have hH : ContDiffAt ℝ ∞ H (0,z) := hHS.contDiffAt (hS.mem_nhds hHere)
  have hδ : |(1:Mat) i j| ≤ 1 := by by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
  have hProduct := quadratic_product_remainder_directional_bound S0 R0 H (0,z) (1,0) (0,b) ((1:Mat) i j) r ‖a‖ ‖b‖
    hS0 hR0 hH hδ (norm_nonneg _) (norm_nonneg _) Q (Q*(1+C)) (Q*N) (Q*(1+2*C)*N)
    |parallelDensityCenterBudget hm K M N Z| |parallelDensityMixedBudget hm K M N Z| H0 HC HZ HM
    hQ (by positivity) (by positivity) (by positivity) (abs_nonneg _) (abs_nonneg _) hH0 hHC hHZ hHM
    hNv hScalar.1 hScalar.2.1 hScalar.2.2
    (hRem.2.2.1.trans (by gcongr;exact le_abs_self _))
    (hRem.2.2.2.trans (by gcongr;exact le_abs_self _)) hHv hHc hHz hHm
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ E (y,r • L z) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv.le⟩))
  have hx : E (y,r • L z) ∈ Ω := by
    simpa only [one_smul] using hN.path_image hy (r • L z) hv.le (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
  have hEI : ContinuousAt (E ∘ parallelFrameInput g y a r L) (0,z) := by
    have hEAt : ContinuousAt E (parallelFrameInput g y a r L (0,z)) := by
      simpa only [parallelFrameInput,affineParallelFrame_zero,zero_smul,add_zero] using hE.continuousAt
    exact hEAt.comp (contDiff_parallelFrameInput g y a r L).continuous.continuousAt
  have hImage : E (parallelFrameInput g y a r L (0,z)) ∈ Ω := by
    simpa only [parallelFrameInput,affineParallelFrame_zero,zero_smul,add_zero] using hx
  have hNear : (fun p => parallelNormalizedFirstCoefficientRemainder g g₁ E y a r L p i j) =ᶠ[𝓝 (0,z)]
      (fun p => (1:Mat) i j*R0 p+S0 p*(H p-(1:Mat) i j)) := by
    filter_upwards [hS.mem_nhds hHere,hEI.eventually (hΩ.mem_nhds hImage)] with p hpS hpΩ
    exact h.parallelNormalizedFirstCoefficientRemainder_eq hK E y a r L p hpΩ (isUnit_iff_ne_zero.mpr (hNe p hpS)) i j
  rw [hNear.fderiv_eq,hNear.fderiv.fderiv_eq]
  exact hProduct

end ShrinkingSpheres
