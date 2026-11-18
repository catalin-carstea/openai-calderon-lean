import Proof.RelativeCenterErrorCoefficientFamily
import Proof.NormalizedRelativeAngularCurve
import Proof.FrameDuality
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def relativeFrameCompose (p : NormalFrameRelativeParameter) (R : X →L[ℝ] X) :
    NormalFrameRelativeParameter := ((p.1.1,p.1.2.comp R),p.2)

lemma relativeParallelCenterError_frame_compose (g : MetricField) (E : X × X → X) (r : ℝ)
    (p : NormalFrameRelativeParameter) (R : X →L[ℝ] X) (z : X) :
    normalFrameRelativeParallelCenterError g E r (relativeFrameCompose p R,z) =
      normalFrameRelativeParallelCenterError g E r (p,R z) := rfl

lemma relativeCenterErrorWeight_frame_compose (g : MetricField) (E : X × X → X) (r : ℝ) (a : X)
    (p : NormalFrameRelativeParameter) (R : X →L[ℝ] X) (k : I) (z : X) :
    normalFrameRelativeCenterErrorWeight g E r a k (relativeFrameCompose p R,z) =
      ∑ l : I,(R (axis k)) l*normalFrameRelativeCenterErrorWeight g E r a l (p,R z) := by
  let C : X →L[ℝ] ℝ := (metricBilinear g p.1.1
    (normalFrameRelativeParallelCenterError g E r (p,R z) a)).comp p.1.2
  have hh := linear_axis_expansion C (R (axis k))
  change metricPair g p.1.1 (normalFrameRelativeParallelCenterError g E r (relativeFrameCompose p R,z) a)
    (p.1.2 (R (axis k))) = _
  rw [relativeParallelCenterError_frame_compose]
  simpa only [C,ContinuousLinearMap.comp_apply,metricBilinear_apply,
    normalFrameRelativeCenterErrorWeight] using hh

lemma RelativeCenterErrorCoefficientFamily.scalar_rotation_germ_at
    {d : Data} {y a : X} {CC CH : ℝ}
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (hp : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0)
    (i j : I) :
    ∀ᶠ θ in 𝓝 (0:ℝ),∀ k : I,∀ w : UnitSphere,
      (C k).scalar (normalFrameRelativeAngularCurve d.γ p i j θ,w.val) =
        ∑ l : I,(coordinateRotationIsometry i j θ (axis k)) l*
          (C l).scalar (p,coordinateRotationIsometry i j θ w.val) := by
  have hFix : normalFrameRelativeNormalization d.γ p=p := normalFrameRelativeNormalization_eq_self _ _ he
  have hCurve0 : normalFrameRelativeAngularCurve d.γ p i j 0=p := by
    rw [normalFrameRelativeAngularCurve_zero,hFix]
  have hEach (k : I) : ∀ᶠ θ in 𝓝 (0:ℝ),normalFrameRelativeAngularCurve d.γ p i j θ ∈ (C k).domain := by
    have h0 : normalFrameRelativeAngularCurve d.γ p i j 0 ∈ (C k).domain := by
      rw [hCurve0]
      exact hp k
    exact (hasDerivAt_normalFrameRelativeAngularCurve d.γ p i j).continuousAt.eventually ((C k).isOpen.mem_nhds h0)
  filter_upwards [Filter.eventually_all.mpr hEach] with θ hθ
  intro k w
  have hw : w.val ∈ Metric.closedBall (0:X) 2 :=
    Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
  have hR (z : X) : ‖coordinateRotationIsometry i j θ z‖=‖z‖ := (coordinateRotationIsometry i j θ).norm_map z
  have hRw : coordinateRotationIsometry i j θ w.val ∈ Metric.closedBall (0:X) 2 := by
    simpa only [Metric.mem_closedBall,dist_zero_right,hR] using hw
  have hLeft := ((C k).actual _ (hθ k) w.val hw).eq_of_nhds
  have hRight (l : I) := ((C l).actual p (hp l) _ hRw).eq_of_nhds
  have hCompose : normalFrameRelativeAngularCurve d.γ p i j θ =
      relativeFrameCompose p (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap := by
    simp only [normalFrameRelativeAngularCurve,hFix,relativeFrameCompose]
  calc
    _ = normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a k
        (normalFrameRelativeAngularCurve d.γ p i j θ,w.val) := hLeft
    _ = ∑ l : I,(coordinateRotationIsometry i j θ (axis k)) l*
        normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a l
          (p,coordinateRotationIsometry i j θ w.val) := by
      rw [hCompose]
      exact relativeCenterErrorWeight_frame_compose _ _ _ _ _ _ _ _
    _ = _ := Finset.sum_congr rfl (fun l _ => congrArg
      (fun z : ℝ => (coordinateRotationIsometry i j θ (axis k)) l*z) (hRight l).symm)
lemma RelativeCenterErrorCoefficientFamily.scalar_rotation_germ
    {d : Data} {y a : X} {CC CH : ℝ}
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (he : ∀ k l,metricPair d.γ y (d.frame y k) (d.frame y l) = if k=l then 1 else 0)
    (i j : I) :
    ∀ᶠ θ in 𝓝 (0:ℝ),∀ k : I,∀ w : UnitSphere,
      (C k).scalar (normalFrameRelativeAngularCurve d.γ ((y,frameVectorLinear d.frame y),0) i j θ,w.val) =
        ∑ l : I,(coordinateRotationIsometry i j θ (axis k)) l*
          (C l).scalar (((y,frameVectorLinear d.frame y),0),coordinateRotationIsometry i j θ w.val) := by
  apply scalar_rotation_germ_at C _ (fun k => (C k).point)
  intro k l
  simpa only [frameVectorLinear_apply,frameVector_axis] using he k l
end ShrinkingSpheres
