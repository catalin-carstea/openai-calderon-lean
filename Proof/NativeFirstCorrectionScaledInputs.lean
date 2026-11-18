import Proof.NativePhysicalFirstCorrectionFamily
import Proof.NormalFrameScaledJetBounds
import Proof.SmoothFiniteJetApply
import Proof.ScaledNormalFrameHorizontalInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma normalizedFirstCorrectionCovector_jet_bound (g g₁ : MetricField)
    (y : X) (L : X →L[ℝ] X) (N : ℕ) (B BR : ℝ)
    (hq : SmoothFiniteJetBound (normalFrameRelativeFirstCovector g g₁) ((y,L),0) N B)
    (hR : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor ((y,L),0) N BR)
    (hs : ContDiffAt ℝ ∞ (normalizedFirstCorrectionCovector g g₁) ((y,L),0)) :
    SmoothFiniteJetBound (normalizedFirstCorrectionCovector g g₁) ((y,L),0) N (2^N*BR*B) := by
  have hProduct := hR.scalar hq
  have hEq : normalizedFirstCorrectionCovector g g₁ =ᶠ[𝓝 (((y,L),0):NormalFrameRelativeParameter)]
      (fun p => normalFrameRelativeInverseRadiusFactor p • normalFrameRelativeFirstCovector g g₁ p) := by
    have hOpen : IsOpen {p : NormalFrameRelativeParameter | 1+p.2 ≠ 0} :=
      isOpen_ne.preimage (continuous_const.add continuous_snd)
    filter_upwards [hOpen.mem_nhds (by simp)] with p hp
    exact normalizedFirstCorrectionCovector_eq_inverse_relative g g₁ p hp
  refine ⟨hProduct.nonneg,hs,?_⟩
  intro n hn
  rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hProduct.bound n hn

lemma relativeRadiusFactor_smooth_finite_jet_bound (y : X) (L : X →L[ℝ] X) (N : ℕ) :
    SmoothFiniteJetBound (fun p : NormalFrameRelativeParameter => 1+p.2) ((y,L),0) N 1 := by
  refine ⟨zero_le_one,contDiffAt_const.add contDiffAt_snd,?_⟩
  intro n hn
  by_cases hn0 : n=0
  · subst n
    norm_num
  · change ‖iteratedFDeriv ℝ n (fun p => 1+relativeRadiusProjectionL p) ((y,L),0)‖ ≤ 1
    rw [norm_iteratedFDeriv_affine_clm_positive relativeRadiusProjectionL 1 ((y,L),0) n (by omega)]
    split_ifs
    · exact norm_relativeRadiusProjectionL_le_one
    · norm_num

/-- The radius factor cancels the apparent beta loss in the native scalar.
The bound concerns the same scalar used in the physical correction. -/
lemma nativePhysicalFirstCorrectionScalar_scaled_three_jets
    (d : Data) (r0 β : ℝ) (y b : X) (L : X →L[ℝ] X) (B : ℝ)
    (hr0 : 0 ≤ r0) (hβ : 1 ≤ β) (hrβ : r0*β ≤ 1)
    (hLog : SmoothFiniteJetBound (normalFrameScaledLogCovector d.radius β y) ((0,L),0) 3 B) :
    SmoothFiniteJetBound (nativePhysicalFirstCorrectionScalar d r0 b ∘
      normalFrameRelativeScaledParameter β y) ((0,L),0) 3 ((8*B)*‖b‖) := by
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  have hFactor := relativeRadiusFactor_smooth_finite_jet_bound (0:X) L 3
  have hEval := hLog.apply_const b
  have hProduct := (hFactor.scalar hEval).const_smul (r0*β)
  have hEq : nativePhysicalFirstCorrectionScalar d r0 b ∘ normalFrameRelativeScaledParameter β y =
      fun p : NormalFrameRelativeParameter => (r0*β) • ((1+p.2) •
        (normalFrameScaledLogCovector d.radius β y p b)) := by
    funext p
    change r0*(1+p.2)*fderiv ℝ (fun x => Real.log (d.radius x)) (y+β⁻¹ • p.1.1) b =
      (r0*β)*((1+p.2)*(β⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) (y+β⁻¹ • p.1.1) b))
    field_simp
  rw [hEq]
  apply hProduct.weaken
  rw [abs_of_nonneg (mul_nonneg hr0 hβpos.le)]
  have hB := hLog.nonneg
  calc
    _ = (r0*β)*((8*B)*‖b‖) := by ring
    _ ≤ 1*((8*B)*‖b‖) := mul_le_mul_of_nonneg_right hrβ (by positivity)
    _ = _ := one_mul _

end ShrinkingSpheres
