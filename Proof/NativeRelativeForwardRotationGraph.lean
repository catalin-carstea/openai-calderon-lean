import Proof.NativeRelativeRadialRotationCovariance
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

/-- The normalized angular derivative of the chosen native quadratic
    remainder is its actual H2 distributional rotation commutator at every
    parameter in the normalization-stable domain. -/
theorem native_relative_forward_rotation_distribution
    {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C}
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (i j : I) (f : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (t.forwardTaylor p (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (normalFrameRelativeAngularDerivative d.γ t.forwardTaylor i j p
          (sphereSobolevInclusionL 2 1 (by norm_num) f)+
            t.forwardTaylor p (sphereSobolevRotationL 2 i j f)) := by
  let c := normalFrameRelativeAngularCurve d.γ p i j
  let Q := fun θ => t.response (c θ)
  let r := d.radius y
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  let H := t.forwardTaylor
  let B0 := coarseFirstRadialVariationL 1 ell
  let B1 := radialCorrectionSobolevL 1 ell
  let D := radialCorrectionCovectorL (rotationCovector ell i j)
  have hCurve := hasDerivAt_normalFrameRelativeAngularCurve d.γ p i j
  have hZero : c 0 = normalFrameRelativeNormalization d.γ p :=
    normalFrameRelativeAngularCurve_zero d.γ p i j
  have hpN := V.normalizationStable p hp
  have hRDiff : DifferentiableAt ℝ t.response (c 0) := by
    rw [hZero]
    exact (t.smooth.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))).differentiableAt (by simp)
  have hQDiff : DifferentiableAt ℝ Q 0 := hRDiff.comp 0 hCurve.differentiableAt
  have h0V : c 0 ∈ V.domain := by rw [hZero];exact hpN
  have hEvent : ∀ᶠ θ in 𝓝 (0:ℝ),c θ ∈ V.domain :=
    hCurve.continuousAt.eventually (V.domainOpen.mem_nhds h0V)
  have hNormR := t.response_normalization hZ h hK p (V.sub hp) (V.sub hpN)
  have hCov : ∀ᶠ θ in 𝓝 (0:ℝ),∀ u,Q θ (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ) u) =
      sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ) (Q 0 u) := by
    filter_upwards [hEvent] with θ hθ
    intro u
    have hOp := native_relative_radial_rotation_covariance t V h hK hZ p hp i j θ hθ
    have hValue := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) hOp
    change t.response (c θ) (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ) u) =
      sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ) (t.response (c 0) u)
    rw [hZero,hNormR]
    exact hValue
  have hCompat (v : SphereSobolev 1) : sphereSobolevInclusionL 1 0 (by norm_num) (B1 v) =
      B0 (sphereSobolevInclusionL 1 0 (by norm_num) v) := by
    simpa only [B1,B0,coarseFirstRadialVariationL_normalized_covector,inv_one,one_smul] using radialCorrectionSobolevL_coarse ell v
  have hComm : (sphereSobolevRotationL 1 i j).comp B1-B0.comp (sphereSobolevRotationL 1 i j) =
      D.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    simpa only [B1,B0,D,coarseFirstRadialVariationL_normalized_covector,inv_one,one_smul] using rotation_radialCorrection_commutator i j ell
  have hFirst := hasDerivAt_firstRadial_rotation_zero 1 ell i j
  simp only [inv_one,one_smul] at hFirst
  let Pre : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 0) (SphereSobolev 0)).flip (sphereSobolevInclusionL 1 0 (by norm_num))
  have hPre := Pre.hasFDerivAt.comp_hasDerivAt (0:ℝ) hFirst
  have hFirstModel : (fun t => H (c t)) = fun t => Q t-r •
      (coarseFirstRadialVariationL 1 (ell.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).comp
        (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    funext θ
    change t.forwardTaylor (c θ) = _
    unfold NormalFrameRelativeResponsePacket.forwardTaylor
    rw [h.normalFrameRelativeFirstCovector_angular_curve hK d.g₁ p (q.positive (t.sub (V.sub hp))) i j θ]
  have hD := hQDiff.hasDerivAt.sub (hPre.const_smul r)
  change HasDerivAt (fun t => Q t-r •
    (coarseFirstRadialVariationL 1 (ell.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))
        (deriv Q 0-r • D.comp (sphereSobolevInclusionL 1 0 (by norm_num))) 0 at hD
  rw [← hFirstModel] at hD
  have hC := hD.deriv
  have hPoint : H p = Q 0-r • B0.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    dsimp only [Q]
    rw [hZero,hNormR]
    rfl
  have hHDiff : DifferentiableAt ℝ H (normalFrameRelativeNormalization d.γ p) :=
    (t.contDiffOn_forwardTaylor.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))).differentiableAt (by simp)
  have hCDef := normalFrameRelativeAngularDerivative_eq_curve d.γ H i j p hHDiff
  change normalFrameRelativeAngularDerivative d.γ H i j p = deriv (fun θ => H (c θ)) 0 at hCDef
  have hGraph := radial_taylor_rotation_commutator_distribution_of_germ i j r Q (deriv Q 0) (deriv (fun t => H (c t)) 0)
    B0 D B1 hQDiff.hasDerivAt hCov hCompat hComm hC f
  simpa only [← hPoint,← hCDef] using hGraph


end ShrinkingSpheres
