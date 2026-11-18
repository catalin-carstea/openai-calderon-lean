import Proof.NormalFrameRotationCoefficient
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

/-- The actual local master midpoint operator has the genuine boundary
    rotation covariance whenever the rotated frame remains in its native
    inverse neighborhood. The actual weak solution proves the covariance. -/
theorem normalFrame_radial_rotation_covariance
    (d : Data) (y : X) (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
    (V : Set NormalFrameParameter) (hp0 : (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V)
    (hRep : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
      A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p)))
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
    (hRestrict : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p)))
    (i j : I) (θ : ℝ) (hθ : normalFrameRotationCurve d.frame d.radius y i j θ ∈ V) :
    (R (normalFrameRotationCurve d.frame d.radius y i j θ)).comp
      (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ)) =
      (sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ)).comp
        (R (y,(d.radius y,frameVectorLinear d.frame y))) := by
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let pθ := normalFrameRotationCurve d.frame d.radius y i j θ
  let e := coordinateRotationIsometry i j θ
  let a0 : ℝ × X → Mat := fun q => A (p0,q.2)
  have ha0 : ContDiff ℝ ∞ a0 := hA.comp (contDiff_const.prodMk contDiff_snd)
  let b : ℝ × X → Mat := fun q => coordinateRotationPrincipalFamily i j a0 ((q.1,0),q.2)
  have hb : ContDiff ℝ ∞ b := (contDiff_coordinateRotationPrincipalFamily i j a0 ha0).comp
    ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hPoint (z : X) (hzBall : z ∈ (ballOpens:Set X)) :
      A (pθ,z) = orthogonalPrincipalCoefficient e (fun w => A (p0,w)) z := by
    have hzRot : coordinateRotation i j θ z ∈ Metric.closedBall (0:X) 2 := by
      simpa only [Metric.mem_closedBall,dist_zero_right,coordinateRotation_norm] using unitBall_subset_closedBall_two hzBall
    have hBase := (hRep p0 hp0 (coordinateRotation i j θ z) hzRot).eq_of_nhds
    have hAt := (hRep pθ hθ z (unitBall_subset_closedBall_two hzBall)).eq_of_nhds
    apply hAt.trans
    change normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap
      ((y,(d.radius y,(frameVectorLinear d.frame y).comp e.toContinuousLinearEquiv.toContinuousLinearMap)),z) = _
    rw [normalFrameNormalizedCoefficient_coordinate_rotation]
    rw [← coordinateRotationPrincipalFamily_eq_orthogonal i j a0 θ (0:ℝ) z]
    change (coordinateRotationMatrix i j θ).transpose*
      normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap (p0,coordinateRotation i j θ z)*coordinateRotationMatrix i j θ =
      (coordinateRotationMatrix i j θ).transpose*A (p0,coordinateRotation i j θ z)*coordinateRotationMatrix i j θ
    exact congrArg (fun M : Mat => (coordinateRotationMatrix i j θ).transpose*M*coordinateRotationMatrix i j θ) hBase.symm
  have hRotMem : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e (fun w => A (p0,w)) z) (0:X) (0:ℝ)) ⊤
      ((volume:Measure X).restrict ballOpens) := by
    simpa only [b,a0,coordinateRotationPrincipalFamily_eq_orthogonal,e] using commonSupportEnergyMemLp b hb θ
  have hEnergy := (nativeWeakEnergy_congr_unitBall (commonSupportEnergyMemLp A hA pθ) hRotMem hPoint).2.2
  change TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA pθ) =
    TauCeti.PDE.energyFormH1L0 hRotMem at hEnergy
  have hRotCoercive : IsCoercive (TauCeti.PDE.energyFormH1L0 hRotMem) := by
    rw [← hEnergy]
    exact hCoercive pθ hθ
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  have hF0 (z : X) (_hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F p0) z = A (p0,z) := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
  have hFθ (z : X) (hzBall : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F pθ) z =
      orthogonalPrincipalCoefficient e (fun w => A (p0,w)) z := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hPoint z hzBall
  have hPoisson := strongPoissonL_orthogonal_covariance e (fun w => A (p0,w))
    (hA.continuous.comp (continuous_const.prodMk continuous_id)) (commonSupportEnergyMemLp A hA p0)
      hRotMem (hCoercive p0 hp0) hRotCoercive (F p0) (F pθ) hF0 hFθ (hStrong p0 hp0) (hStrong pθ hθ)
  exact midpointRadial_orthogonal_covariance e (F p0) (F pθ) (R p0) (R pθ)
    (hRestrict p0 hp0) (hRestrict pθ hθ) (actualHighRadialErrorL_orthogonal_covariance e (F p0) (F pθ) hPoisson)

end ShrinkingSpheres
