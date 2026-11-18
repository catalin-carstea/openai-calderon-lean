import Proof.EnlargedFramedEllipticity
import Proof.FrameBasis
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalChart (expMap : X × X → X) (e : Frame) (y : X) (r : ℝ) : X → X :=
  fun z => expMap (y,r • frameVector e y z)

lemma frameVectorLinear_bijective (γ : MetricField) (e : Frame) (y : X)
    (hFrame : ∀ i j,metricPair γ y (e y i) (e y j) = if i=j then 1 else 0) :
    Function.Bijective (frameVectorLinear e y) := by
  have hInj : Function.Injective (frameVectorLinear e y) := by
    intro u v huv
    have hZero : frameVector e y (u-v) = 0 := by
      rw [← frameVectorLinear_apply,map_sub,huv,sub_self]
    have hN := metricPair_frameVector_self γ e y (u-v) hFrame
    rw [hZero] at hN
    have hN0 : ‖u-v‖^2 = 0 := by simpa only [metricPair,PiLp.zero_apply,mul_zero,Finset.sum_const_zero] using hN.symm
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hN0))
  exact ⟨hInj,(LinearMap.injective_iff_surjective (f:=(frameVectorLinear e y).toLinearMap)).mp hInj⟩

lemma contDiff_normalChart_input (e : Frame) (y : X) (r : ℝ) :
    ContDiff ℝ ∞ (fun z : X => (y,r • frameVector e y z)) :=
  contDiff_const.prodMk ((contDiff_frameVector_fixed e y).const_smul r)

lemma NormalCoordinates.smoothNear_normalChart {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R y) :
    smoothNear (normalChart expMap e y r) (Metric.closedBall (0:X) 1) := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  let input : X → X × X := fun z => (y,r • frameVector e y z)
  have hI : ContDiff ℝ ∞ input := contDiff_normalChart_input e y r
  refine ⟨input ⁻¹' U,hU.preimage hI.continuous,?_,?_⟩
  · intro z hz
    apply hTube
    refine ⟨hy,?_⟩
    have hw := scaled_unitDisk_mem_disk γ y (frameVector e y z) r (frameVector_mem_unitDisk γ e y z hFrame hz)
    exact hw.trans ((sq_le_sq₀ hr.le (hr.le.trans hrR)).2 hrR)
  · exact hReg.comp hI.contDiffOn (fun z hz => hz)

lemma NormalCoordinates.hasFDerivAt_normalChart {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (r : ℝ) (z : X) (hv : r • frameVector e y z ∈ disk γ y (R y)) :
    HasFDerivAt (normalChart expMap e y r)
      ((normalVerticalJacobian expMap y (r • frameVector e y z)).comp (r • frameVectorLinear e y)) z := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,r • frameVector e y z)) (y,r • frameVector e y z) :=
    ((hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))).differentiableAt (by simp)).hasFDerivAt
  have hInput : HasFDerivAt (fun w : X => (y,r • frameVector e y w))
      ((0 : X →L[ℝ] X).prod (r • frameVectorLinear e y)) z := by
    simpa only [Pi.smul_apply,frameVectorLinear_apply] using
      (hasFDerivAt_const (𝕜:=ℝ) y z).prodMk ((frameVectorLinear e y).hasFDerivAt.const_smul r)
  have hd : HasFDerivAt (normalChart expMap e y r)
      ((fderiv ℝ expMap (y,r • frameVector e y z)).comp
        ((0 : X →L[ℝ] X).prod (r • frameVectorLinear e y))) z := hE.comp z hInput
  apply hd.congr_fderiv
  ext u
  simp only [normalVerticalJacobian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.prod_apply,_root_.zero_apply]

lemma NormalCoordinates.normalChart_derivative_bijective {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (r : ℝ) (hr : 0 < r) (z : X) (hv : r • frameVector e y z ∈ disk γ y (R y)) :
    Function.Bijective (fderiv ℝ (normalChart expMap e y r) z) := by
  rw [(hN.hasFDerivAt_normalChart hy e r z hv).fderiv]
  have hFB := frameVectorLinear_bijective γ e y hFrame
  have hScale : Function.Bijective (r • frameVectorLinear e y : X →L[ℝ] X) := by
    constructor
    · intro a b hab
      apply hFB.1
      change r • frameVectorLinear e y a = r • frameVectorLinear e y b at hab
      have hh := congrArg (fun w : X => r⁻¹ • w) hab
      simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] using hh
    · intro w
      obtain ⟨a,ha⟩ := hFB.2 (r⁻¹ • w)
      refine ⟨a,?_⟩
      change r • frameVectorLinear e y a = w
      rw [ha,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  obtain ⟨E,hE⟩ := hN.normalVerticalJacobian_isInvertible hy (r • frameVector e y z) hv
  rw [← hE]
  exact E.bijective.comp hScale

lemma normalChart_velocity_mem (γ : MetricField) (e : Frame) (y : X)
    (hFrame : ∀ i j,metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (r R : ℝ) (hr : 0 ≤ r) (hrR : r ≤ R) {z : X} (hz : z ∈ Metric.closedBall (0:X) 1) :
    r • frameVector e y z ∈ disk γ y R := by
  have hw := scaled_unitDisk_mem_disk γ y (frameVector e y z) r (frameVector_mem_unitDisk γ e y z hFrame hz)
  exact hw.trans ((sq_le_sq₀ hr (hr.trans hrR)).2 hrR)

/-- Interior points of the fixed ball map to the actual physical ball interior.
    This follows from the admitted invertible differential and the inverse function theorem. -/
theorem NormalCoordinates.normalChart_mem_interior {Y Ω : Set X} {γ : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R y) {z : X} (hz : z ∈ Metric.ball (0:X) 1) :
    normalChart expMap e y r z ∈ interior (closedBallImage γ expMap (fun _ => r) y) := by
  have hzClosed : z ∈ Metric.closedBall (0:X) 1 := Metric.ball_subset_closedBall hz
  obtain ⟨S,hS,hIn,hF⟩ := hN.smoothNear_normalChart hy e hFrame r hr hrR
  have hStrict := (hF.contDiffAt (hS.mem_nhds (hIn hzClosed))).hasStrictFDerivAt (by simp)
  have hBij := hN.normalChart_derivative_bijective hy e hFrame r hr z
    (normalChart_velocity_mem γ e y hFrame r (R y) hr.le hrR hzClosed)
  have hRange : (fderiv ℝ (normalChart expMap e y r) z).range = ⊤ :=
    LinearMap.range_eq_top.mpr hBij.2
  have hMap := hStrict.map_nhds_eq_of_surj hRange
  have hImage : normalChart expMap e y r '' Metric.ball (0:X) 1 ∈ 𝓝 (normalChart expMap e y r z) := by
    rw [← hMap]
    exact Filter.image_mem_map (Metric.isOpen_ball.mem_nhds hz)
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset hImage ?_
  rintro w ⟨a,ha,rfl⟩
  refine ⟨r • frameVector e y a,?_,rfl⟩
  exact normalChart_velocity_mem γ e y hFrame r r hr.le le_rfl (Metric.ball_subset_closedBall ha)

end ShrinkingSpheres
