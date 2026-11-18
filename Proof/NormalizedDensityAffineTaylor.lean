import Proof.NormalizedDensityZeroJets
import Proof.StrictNormalSegmentBounds
import Proof.MixedCenterTaylor
import Proof.VerticalZeroJetTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- All four actual affine Taylor estimates use the same normalized scalar
    family and canonical first differential: value, vertical, center and mixed. -/
theorem Background.normalized_joint_density_affine_taylor {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    let F := normalizedJointFirstDensityFactor g g₁ E
    let ell := firstDensityLogDifferential g g₁
    let Q := backgroundNormalizedDensityJetBudget hm K M
    ‖F (y,v)-1-ell y v‖ ≤ Q*‖v‖^2 ∧
    (∀ b : X,‖fderiv ℝ F (y,v) (0,b)-ell y b‖ ≤ Q*‖v‖*‖b‖) ∧
    (∀ a : X,‖fderiv ℝ F (y,v) (a,0)-fderiv ℝ ell y a v‖ ≤ Q*‖v‖^2*‖a‖) ∧
    (∀ a b : X,‖fderiv ℝ (fderiv ℝ F) (y,v) (0,b) (a,0)-fderiv ℝ ell y a b‖ ≤ Q*‖v‖*‖b‖*‖a‖) := by
  dsimp only
  let F := normalizedJointFirstDensityFactor g g₁ E
  let ell := firstDensityLogDifferential g g₁
  let Q := backgroundNormalizedDensityJetBudget hm K M
  have hV := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hQ : 0 ≤ Q := by dsimp [Q,backgroundNormalizedDensityJetBudget];positivity
  have hSegment (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ContDiffAt ℝ ∞ F (y,t • v) ∧ ∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n F (y,t • v)‖ ≤ Q := by
    obtain ⟨htStrict,htNorm⟩ := h.1.strict_normal_segment_bounds hK (hN.center_mem hy) v (R y) hv hv1 ht
    exact h.normalized_joint_first_density_jets hY hΩ hK hm hN hR hy (t • v) htStrict htNorm
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hF0 : ContDiffAt ℝ ∞ F (y,0) := by simpa only [zero_smul] using (hSegment 0 hz).1
  have hSmooth (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ F (y,t • v) := (hSegment t ht).1
  have hSecond (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖fderiv ℝ (fderiv ℝ F) (y,t • v)‖ ≤ Q := by
    have hb := (hSegment t ht).2 2 (by omega)
    rwa [← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hb
  have hThird (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v)‖ ≤ Q := by
    have hb := (hSegment t ht).2 3 (by omega)
    rwa [← norm_iteratedFDeriv_fderiv (n:=2),← norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] at hb
  have hVertical (b : X) : (fun x => fderiv ℝ F (x,0) (0,b)) =ᶠ[𝓝 y] (fun x => ell x b) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact h.normalized_joint_density_vertical_zero hY hΩ hK hN hx b
  have hEll : ContDiffAt ℝ ∞ ell y :=
    (h.firstDensityLogDifferential_smooth hK hΩ).contDiffAt (hΩ.mem_nhds (hN.center_mem hy))
  have hMixed (a b : X) : fderiv ℝ (fderiv ℝ F) (y,0) (0,b) (a,0) = fderiv ℝ ell y a b := by
    have hb := center_velocity_second_fderiv_eq_of_slice F y a b (fun x => ell x b) hF0 (hVertical b)
    have hEval := (hEll.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const b y)
    have hValue := congrArg (fun L : X →L[ℝ] ℝ => L a) hEval.fderiv
    simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      zero_apply,map_zero,zero_add] at hValue
    exact hb.trans hValue
  have hCenterZero (a : X) : fderiv ℝ F (y,0) (a,0) = 0 := by
    have hNear : (fun x => F (x,0)) =ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
      filter_upwards [hY.mem_nhds hy] with x hx
      exact hN.normalized_joint_density_zero hx
    have hInput : HasFDerivAt (fun x : X => (x,(0:X))) (ContinuousLinearMap.inl ℝ X X) y :=
      (hasFDerivAt_id y).prodMk (hasFDerivAt_const (0:X) y)
    have hComp := (hF0.differentiableAt (by simp)).hasFDerivAt.comp y hInput
    simp only [Function.comp_def] at hComp
    have hb := congrArg (fun L : X →L[ℝ] ℝ => L a) hNear.fderiv_eq
    rw [hComp.fderiv] at hb
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,fderiv_const_apply,zero_apply] using hb
  have hAffine := vertical_affine_jet_taylor F y v hSmooth Q hQ hSecond
  have hZeroValue : F (y,0) = 1 := hN.normalized_joint_density_zero hy
  have hZeroVertical (b : X) : fderiv ℝ F (y,0) (0,b) = ell y b :=
    h.normalized_joint_density_vertical_zero hY hΩ hK hN hy b
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hZeroValue,hZeroVertical] using hAffine.1
  · intro b
    simpa only [hZeroVertical] using hAffine.2 b
  · intro a
    have hb := norm_center_fderiv_affine_error_of_third_bound F y a v hSmooth Q hQ hThird
    simpa only [hCenterZero,hMixed,sub_zero] using hb
  · intro a b
    have hb := norm_center_velocity_second_fderiv_sub_zero_of_third_bound F y a v b hSmooth Q hQ hThird
    simpa only [hMixed] using hb

end ShrinkingSpheres
