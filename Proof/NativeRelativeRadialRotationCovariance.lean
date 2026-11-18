import Proof.NativeRelativeTrueAdjointDomain
import Proof.RelativeAngularCoefficientCovariance
import Proof.MidpointRadialOrthogonalCovariance
import Proof.NativeWeakCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Actual native relative radial covariance on a single common inverse
    domain, valid at every positive independent parameter. -/
theorem native_relative_radial_rotation_covariance
    {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C}
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (i j : I) (θ : ℝ) (hθ : normalFrameRelativeAngularCurve d.γ p i j θ ∈ V.domain) :
    (t.response (normalFrameRelativeAngularCurve d.γ p i j θ)).comp
      (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ)) =
      (sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ)).comp (t.response p) := by
  let pθ := normalFrameRelativeAngularCurve d.γ p i j θ
  let e := coordinateRotationIsometry i j θ
  let a0 : ℝ × X → Mat := fun v => q.a (p,v.2)
  have ha0 : ContDiff ℝ ∞ a0 := q.smooth.comp (contDiff_const.prodMk contDiff_snd)
  let b : ℝ × X → Mat := fun q => coordinateRotationPrincipalFamily i j a0 ((q.1,0),q.2)
  have hb : ContDiff ℝ ∞ b := (contDiff_coordinateRotationPrincipalFamily i j a0 ha0).comp
    ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hPoint (z : X) (hzBall : z ∈ (ballOpens:Set X)) :
      q.a (pθ,z) = orthogonalPrincipalCoefficient e (fun w => q.a (p,w)) z := by
    have hzRot : coordinateRotation i j θ z ∈ Metric.closedBall (0:X) 2 := by
      simpa only [Metric.mem_closedBall,dist_zero_right,coordinateRotation_norm] using unitBall_subset_closedBall_two hzBall
    have hBase := (q.coefficientGerm p (t.sub (V.sub hp)) (coordinateRotation i j θ z)
      (Metric.closedBall_subset_closedBall hZ hzRot)).eq_of_nhds
    have hAt := (q.coefficientGerm pθ (t.sub (V.sub hθ)) z
      (Metric.closedBall_subset_closedBall hZ (unitBall_subset_closedBall_two hzBall))).eq_of_nhds
    apply hAt.trans
    have hCurve := h.normalFrameRelativeCoefficient_angular_curve hK d.g₁ d.expMap (d.radius y)
      p (q.positive (t.sub (V.sub hp))) i j θ z
    exact hCurve.trans (by
      rw [← coordinateRotationPrincipalFamily_eq_orthogonal i j a0 θ (0:ℝ) z]
      change (coordinateRotationMatrix i j θ).transpose*
        normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,coordinateRotation i j θ z)*
          coordinateRotationMatrix i j θ =
        (coordinateRotationMatrix i j θ).transpose*q.a (p,coordinateRotation i j θ z)*
          coordinateRotationMatrix i j θ
      exact congrArg (fun M : Mat => (coordinateRotationMatrix i j θ).transpose*M*coordinateRotationMatrix i j θ) hBase.symm)
  have hRotMem : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e (fun w => q.a (p,w)) z) (0:X) (0:ℝ)) ⊤
      ((volume:Measure X).restrict ballOpens) := by
    simpa only [b,a0,coordinateRotationPrincipalFamily_eq_orthogonal,e] using commonSupportEnergyMemLp b hb θ
  have hEnergy := (nativeWeakEnergy_congr_unitBall (commonSupportEnergyMemLp q.a q.smooth pθ) hRotMem hPoint).2.2
  change TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp q.a q.smooth pθ) =
    TauCeti.PDE.energyFormH1L0 hRotMem at hEnergy
  have hRotCoercive : IsCoercive (TauCeti.PDE.energyFormH1L0 hRotMem) := by
    rw [← hEnergy]
    exact V.coercive pθ hθ
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  have hF0 (z : X) (_hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F p) z = q.a (p,z) := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
  have hFθ (z : X) (hzBall : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F pθ) z =
      orthogonalPrincipalCoefficient e (fun w => q.a (p,w)) z := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hPoint z hzBall
  have hPoisson := strongPoissonL_orthogonal_covariance e (fun w => q.a (p,w))
    (q.smooth.continuous.comp (continuous_const.prodMk continuous_id)) (commonSupportEnergyMemLp q.a q.smooth p)
      hRotMem (V.coercive p hp) hRotCoercive (F p) (F pθ) hF0 hFθ (V.strong p hp) (V.strong pθ hθ)
  exact midpointRadial_orthogonal_covariance e (F p) (F pθ) (t.response p) (t.response pθ)
    (t.highRestriction p (V.sub hp)) (t.highRestriction pθ (V.sub hθ)) (actualHighRadialErrorL_orthogonal_covariance e (F p) (F pθ) hPoisson)


end ShrinkingSpheres
