import Proof.NormalScalarRemainderRotation
import Proof.CommonSupportScalarAngularCoefficient
import Proof.UniformRelativeAngularDerivativeJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
namespace RelativeNormalScalarRemainderFamily
variable {d : Data} {y : X} {CR : ℝ}

lemma scalar_rotation_germ_at (R : RelativeNormalScalarRemainderFamily d y CR)
    {Ω : Set X} {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ R.domain)
    (hpPos : p ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ i j,metricPair d.γ p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j))=if i=j then 1 else 0)
    (i j : I) :
    ∀ᶠ θ : ℝ in 𝓝 0,∀ w : UnitSphere,
      R.scalar (normalFrameRelativeAngularCurve d.γ p i j θ,w.val)=
        R.scalar (p,coordinateRotationIsometry i j θ w.val) := by
  have hFix := normalFrameRelativeNormalization_eq_self d.γ p he
  have h0 : normalFrameRelativeAngularCurve d.γ p i j 0=p :=
    (normalFrameRelativeAngularCurve_zero d.γ p i j).trans hFix
  have h0Mem : normalFrameRelativeAngularCurve d.γ p i j 0 ∈ R.domain := by
    rw [h0]
    exact hp
  have hNear : ∀ᶠ θ : ℝ in 𝓝 0,normalFrameRelativeAngularCurve d.γ p i j θ ∈ R.domain :=
    (hasDerivAt_normalFrameRelativeAngularCurve d.γ p i j).continuousAt.eventually
      (R.isOpen.mem_nhds h0Mem)
  filter_upwards [hNear] with θ hθ
  intro w
  have hw : w.val ∈ Metric.closedBall (0:X) 2 := Metric.closedBall_subset_closedBall (by norm_num)
    (Metric.sphere_subset_closedBall w.property)
  have hRw : coordinateRotationIsometry i j θ w.val ∈ Metric.closedBall (0:X) 2 := by
    simpa only [Metric.mem_closedBall,dist_zero_right,(coordinateRotationIsometry i j θ).norm_map] using hw
  exact ((R.actual _ hθ w.val hw).eq_of_nhds.trans
    (h.normalScalarRemainder_angular_curve hK (d.radius y) p hpPos i j θ w)).trans
      (R.actual p hp _ hRw).eq_of_nhds.symm

lemma angular_half (R : RelativeNormalScalarRemainderFamily d y CR)
    {Ω : Set X} {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ R.domain)
    (hpPos : p ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ i j,metricPair d.γ p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j))=if i=j then 1 else 0)
    (i j : I) :
    closedThreeJetHalfBoundaryScalarMultiplierL (normalFrameRelativeAngularDerivative d.γ R.closed i j p)=
      closedCoefficientAngularHalfL i j (R.closed p) :=
  commonSupportClosedCoefficient_angular_half d.γ R.scalar R.smooth R.support R.compact R.supported p i j
    (R.scalar_rotation_germ_at h hK p hp hpPos he i j)

/-- The same actual normal remainder has gained angular two-jets from
    the existing completed three-jet packet. -/
theorem uniform_angular_two_jets {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) :
    ∃ CG : ℝ,1 ≤ CG ∧ ∀ d : Data,Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ y ∈ Ω,∀ CR : ℝ,∀ R : RelativeNormalScalarRemainderFamily d y CR,
      (∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
        ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0) →
      ∀ i j,SmoothFiniteJetBound (normalFrameRelativeAngularDerivative d.γ R.closed i j)
        ((y,frameVectorLinear d.frame y),0) 2 (CG*(CR*(d.radius y)^2)) := by
  obtain ⟨CG,hCG,hJets⟩ := uniform_relative_angular_derivative_higher_jets (E:=ClosedCoefficientJets 3)
    hΩ 2 hm K M hK
  refine ⟨CG,hCG,?_⟩
  intro d hd y hy CR R he i j
  have hh := hJets d.γ d.g₁ d.g₂ d.frame hd y hy _ he R.closed R.jets.smooth
    (CR*(d.radius y)^2) R.jets.nonneg R.jets.bound i j
  exact ⟨mul_nonneg (zero_le_one.trans hCG) R.jets.nonneg,hh.1,hh.2⟩
end RelativeNormalScalarRemainderFamily
end ShrinkingSpheres
