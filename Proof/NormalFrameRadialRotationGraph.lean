import Proof.NormalFrameRadialRotationCovariance
import Proof.NormalFrameRadialTaylorModel
import Proof.LocalRadialTaylorRotationDistribution

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

/-- The master rotation derivative of the true quadratic Taylor remainder
    is exactly its angular commutator, as a distributional graph on H2 data.
    This identifies the rotation terms removed by the covariant jet bound. -/
theorem Background.normalFrame_radial_taylor_rotation_distribution {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
    (V : Set NormalFrameParameter) (hV : IsOpen V) (hp0 : (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V)
    (hRep : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
      A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
    (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hR : ContDiffOn ℝ ∞ R V)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p)))
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
    (hRestrict : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p)))
    (i j : I) (f : SphereSobolev 2) :
    let H := normalFrameRadialTaylorFamily d R
    let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
    let C := deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0
    sphereSobolevRotationL 0 i j (H p0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+H p0 (sphereSobolevRotationL 2 i j f)) := by
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let c := normalFrameRotationCurve d.frame d.radius y i j
  let Q := fun t => R (c t)
  let r := d.radius y
  let q := firstDensityLogCovector d y
  let H := normalFrameRadialTaylorFamily d R
  let B0 := coarseFirstRadialVariationL 1 q
  let B1 := radialCorrectionSobolevL 1 q
  let D := radialCorrectionCovectorL (rotationCovector q i j)
  have hCurve := hasDerivAt_normalFrameRotationCurve d.frame d.radius y i j
  have hZero : c 0 = p0 := normalFrameRotationCurve_zero d.frame d.radius y i j
  have hRDiff : DifferentiableAt ℝ R (c 0) := by
    rw [hZero]
    exact (hR.contDiffAt (hV.mem_nhds hp0)).differentiableAt (by simp)
  have hQDiff : DifferentiableAt ℝ Q 0 := hRDiff.comp 0 hCurve.differentiableAt
  have h0V : c 0 ∈ V := by rw [hZero];exact hp0
  have hEvent : ∀ᶠ t in 𝓝 (0:ℝ),c t ∈ V := hCurve.continuousAt.eventually (hV.mem_nhds h0V)
  have hCov : ∀ᶠ t in 𝓝 (0:ℝ),∀ u,Q t (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j t) u) =
      sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j t) (Q 0 u) := by
    filter_upwards [hEvent] with t ht
    intro u
    have hOp := normalFrame_radial_rotation_covariance d y A hA S hS hz V hp0 hRep R hCoercive hStrong hRestrict i j t ht
    have hValue := congrArg (fun T => T u) hOp
    simpa only [Q,c,normalFrameRotationCurve_zero,ContinuousLinearMap.comp_apply] using hValue
  have hCompat (v : SphereSobolev 1) : sphereSobolevInclusionL 1 0 (by norm_num) (B1 v) =
      B0 (sphereSobolevInclusionL 1 0 (by norm_num) v) := by
    simpa only [B1,B0,coarseFirstRadialVariationL_normalized_covector,inv_one,one_smul] using radialCorrectionSobolevL_coarse q v
  have hComm : (sphereSobolevRotationL 1 i j).comp B1-B0.comp (sphereSobolevRotationL 1 i j) =
      D.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    simpa only [B1,B0,D,coarseFirstRadialVariationL_normalized_covector,inv_one,one_smul] using rotation_radialCorrection_commutator i j q
  have hFirst := hasDerivAt_firstRadial_rotation_zero 1 q i j
  simp only [inv_one,one_smul] at hFirst
  let Pre : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 0) (SphereSobolev 0)).flip (sphereSobolevInclusionL 1 0 (by norm_num))
  have hPre := Pre.hasFDerivAt.comp_hasDerivAt (0:ℝ) hFirst
  have hFirstModel : (fun t => H (c t)) = fun t => Q t-r •
      (coarseFirstRadialVariationL 1 (q.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).comp
        (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    funext t
    exact h.normalFrameRadialTaylorFamily_rotation hΩ hK hy R i j t
  have hD := hQDiff.hasDerivAt.sub (hPre.const_smul r)
  change HasDerivAt (fun t => Q t-r •
    (coarseFirstRadialVariationL 1 (q.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))
        (deriv Q 0-r • D.comp (sphereSobolevInclusionL 1 0 (by norm_num))) 0 at hD
  rw [← hFirstModel] at hD
  have hC := hD.deriv
  have hPoint : H p0 = Q 0-r • B0.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    dsimp only [Q]
    rw [hZero]
    dsimp only [H,normalFrameRadialTaylorFamily,p0,r,B0,q]
    rw [h.normalFrameFirstCovector_actual hΩ hK hy,radialCorrectionCovectorL_apply]
  have hGraph := radial_taylor_rotation_commutator_distribution_of_germ i j r Q (deriv Q 0) (deriv (fun t => H (c t)) 0)
    B0 D B1 hQDiff.hasDerivAt hCov hCompat hComm hC f
  simpa only [← hPoint] using hGraph

end ShrinkingSpheres
