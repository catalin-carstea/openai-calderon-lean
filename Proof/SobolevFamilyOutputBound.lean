import Proof.SobolevFamilyOutput
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma HarmonicTestExpansion.integrableOn_realSobolevSection_sq {Y : Set X} (hY : IsOpen Y)
    {g : MetricField} {e : Frame} {φ : Field} (E : HarmonicTestExpansion Y g e φ)
    (s : ℝ) (hs : s ≤ 2) (w : X → ℝ) (hw : ContinuousOn w Y) :
    IntegrableOn (fun x => w x*‖E.realSobolevSection s hs x‖^2) Y := by
  have hz : ∀ x ∉ E.supportSet,E.realSobolevSection s hs x=0 :=
    fun x hx => E.realSobolevSection_zero s hs hx
  have hSupp : tsupport (E.realSobolevSection s hs) ⊆ E.supportSet :=
    closure_minimal (fun x hx => by_contra fun hn => hx (hz x hn)) E.compactSupportSet.isClosed
  exact integrableOn_local_weighted_norm_sq hY w hw _ (E.contDiff_realSobolevSection s hs).continuous
    (HasCompactSupport.intro E.compactSupportSet hz) (hSupp.trans E.supportSubset)

lemma HarmonicTestExpansion.integrableOn_imagSobolevSection_sq {Y : Set X} (hY : IsOpen Y)
    {g : MetricField} {e : Frame} {φ : Field} (E : HarmonicTestExpansion Y g e φ)
    (s : ℝ) (hs : s ≤ 2) (w : X → ℝ) (hw : ContinuousOn w Y) :
    IntegrableOn (fun x => w x*‖E.imagSobolevSection s hs x‖^2) Y := by
  have hz : ∀ x ∉ E.supportSet,E.imagSobolevSection s hs x=0 :=
    fun x hx => E.imagSobolevSection_zero s hs hx
  have hSupp : tsupport (E.imagSobolevSection s hs) ⊆ E.supportSet :=
    closure_minimal (fun x hx => by_contra fun hn => hx (hz x hn)) E.compactSupportSet.isClosed
  exact integrableOn_local_weighted_norm_sq hY w hw _ (E.contDiff_imagSobolevSection s hs).continuous
    (HasCompactSupport.intro E.compactSupportSet hz) (hSupp.trans E.supportSubset)

/-- The SAME product output of a uniformly H1-to-L2 family has exactly
    the physical H1 remainder bound required in the principal decomposition. -/
theorem SobolevFamilyOutput.norm_sq_le {Y : Set X} (hY : IsOpen Y) {d : Data}
    (hρ : ContinuousOn (metricDensity d.γ) Y) {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    {H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} (P : SobolevFamilyOutput d E H)
    {C : ℝ} (hC : 0 ≤ C) (hH : ∀ x ∈ Y,‖H x‖ ≤ C) :
    ‖P.output‖^2 ≤ C^2*(∫ x in Y,metricDensity d.γ x*sobolevSq d.γ d.frame 1 x (fun w => φ (x,w))) := by
  have hiR := E.integrableOn_realSobolevSection_sq hY 1 (by norm_num) (metricDensity d.γ) hρ
  have hiI := E.integrableOn_imagSobolevSection_sq hY 1 (by norm_num) (metricDensity d.γ) hρ
  have hEach (x : X) (hx : x ∈ Y) (u : SphereSobolev 1) : ‖H x u‖^2 ≤ C^2*‖u‖^2 := by
    have hn := ((H x).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hH x hx) (norm_nonneg u))
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg u))).mpr hn
  have hR (x : X) (hx : x ∈ Y) : ‖P.realSection x‖^2 ≤ C^2*‖E.realSobolevSection 1 (by norm_num) x‖^2 := by
    rw [P.realEq x hx,LinearIsometryEquiv.norm_map]
    exact hEach x hx _
  have hI (x : X) (hx : x ∈ Y) : ‖P.imagSection x‖^2 ≤ C^2*‖E.imagSobolevSection 1 (by norm_num) x‖^2 := by
    rw [P.imagEq x hx,LinearIsometryEquiv.norm_map]
    exact hEach x hx _
  have hIntR : (∫ x in Y,metricDensity d.γ x*‖P.realSection x‖^2) ≤
      C^2*(∫ x in Y,metricDensity d.γ x*‖E.realSobolevSection 1 (by norm_num) x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun x => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))) (hiR.const_mul (C^2))
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    exact (mul_le_mul_of_nonneg_left (hR x hx) (Real.sqrt_nonneg _)).trans_eq (by dsimp only [metricDensity];ring)
  have hIntI : (∫ x in Y,metricDensity d.γ x*‖P.imagSection x‖^2) ≤
      C^2*(∫ x in Y,metricDensity d.γ x*‖E.imagSobolevSection 1 (by norm_num) x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall (fun x => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))) (hiI.const_mul (C^2))
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    exact (mul_le_mul_of_nonneg_left (hI x hx) (Real.sqrt_nonneg _)).trans_eq (by dsimp only [metricDensity];ring)
  have hMass : (∫ x in Y,metricDensity d.γ x*sobolevSq d.γ d.frame 1 x (fun w => φ (x,w)))=
      (∫ x in Y,metricDensity d.γ x*‖E.realSobolevSection 1 (by norm_num) x‖^2)+
      (∫ x in Y,metricDensity d.γ x*‖E.imagSobolevSection 1 (by norm_num) x‖^2) := by
    rw [← integral_add hiR hiI]
    apply setIntegral_congr_fun hY.measurableSet
    intro x hx
    dsimp only
    rw [E.sobolev_eq_native_sections hFrame 1 (by norm_num) hx,mul_add]
  change ‖P.realization.output‖^2 ≤ _
  rw [P.realization.normSq,hMass,mul_add]
  exact add_le_add hIntR hIntI
end ShrinkingSpheres
