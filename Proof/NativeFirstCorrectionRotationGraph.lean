import Proof.NativePhysicalFirstCorrectionFamily
import Proof.FirstCorrectionAngularFields
import Proof.CoframeCoordinateCombinationAngular
import Proof.RelativeCoframeAngularIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

def nativePhysicalFirstCorrectionAngularFields (d : Data) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) : CoarseAngularFields :=
  firstCorrectionAngularFields (normalizedFirstCorrectionCovector d.γ d.g₁ p)
    (fun j => normalFrameRelativeCoframeValue d.γ b j p) (nativePhysicalFirstCorrectionScalar d r0 b p)

lemma nativePhysicalFirstCorrectionAngularFields_operator (d : Data) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) :
    (nativePhysicalFirstCorrectionAngularFields d r0 b p).operator=nativePhysicalFirstCorrectionFamily d r0 b p := by
  rw [nativePhysicalFirstCorrectionAngularFields,firstCorrectionAngularFields_operator]
  rfl

lemma hasDerivAt_nativeFirstCorrectionRadial_angular_curve {Ω : Set X}
    {K : ℝ} (d : Data) (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω) (i j : I) :
    HasDerivAt (fun θ => firstRadialAdjointOperatorMapL
      (normalizedFirstCorrectionCovector d.γ d.g₁ (normalFrameRelativeAngularCurve d.γ p i j θ)))
      ((CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket
        (normalizedFirstCorrectionCovector d.γ d.g₁ p))).angular (i,j)) 0 := by
  have hCurve := firstRadialAdjointOperatorMapL.hasFDerivAt.comp_hasDerivAt (0:ℝ)
    (hasDerivAt_rotated_covector_zero (normalizedFirstCorrectionCovector d.γ d.g₁ p) i j)
  have hEq : (fun θ => firstRadialAdjointOperatorMapL
      (normalizedFirstCorrectionCovector d.γ d.g₁ (normalFrameRelativeAngularCurve d.γ p i j θ))) =
      (fun θ => firstRadialAdjointOperatorMapL ((normalizedFirstCorrectionCovector d.γ d.g₁ p).comp
        (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap)) := by
    funext θ
    rw [h.normalizedFirstCorrectionCovector_angular_curve hK d.g₁ p hp i j θ]
  rw [hEq]
  exact hCurve

lemma hasDerivAt_nativeFirstCorrection_angular_curve {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} (d : Data) (h : Elliptic Ω K d.γ) (hK : 0 < K) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0)
    (i j : I) :
    HasDerivAt (fun θ => nativePhysicalFirstCorrectionFamily d r0 b
      (normalFrameRelativeAngularCurve d.γ p i j θ))
      ((nativePhysicalFirstCorrectionAngularFields d r0 b p).angular (i,j)) 0 := by
  let c := normalFrameRelativeAngularCurve d.γ p i j
  let P := CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket (normalizedFirstCorrectionCovector d.γ d.g₁ p))
  have hFix := normalFrameRelativeNormalization_eq_self d.γ p he
  have hZero : c 0=p := (normalFrameRelativeAngularCurve_zero d.γ p i j).trans hFix
  have hB := hasDerivAt_nativeFirstCorrectionRadial_angular_curve d h hK p hp i j
  have hMDiff : DifferentiableAt ℝ (relativeCoframeNormalSobolevL 1 d.γ b)
      (normalFrameRelativeNormalization d.γ p) :=
    ((h.contDiffOn_relativeCoframeSobolevMultiplier hΩ hK 1 b).contDiffAt
      ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds
        (h.normalFrameRelativeNormalization_mem hK p hp))).differentiableAt (by simp)
  have hM := (hasDerivAt_relativeAngularFamily d.γ (relativeCoframeNormalSobolevL 1 d.γ b) p i j hMDiff).congr_deriv
    (h.relativeCoframeNormal_angularDerivative hΩ hK 1 b p hp i j)
  have hProd := hB.clm_comp hM
  have hVal :
      (P.angular (i,j)).comp (relativeCoframeNormalSobolevL 1 d.γ b (c 0))+
        (firstRadialAdjointOperatorMapL (normalizedFirstCorrectionCovector d.γ d.g₁ (c 0))).comp
          (relativeCoframeAngularSobolevL 1 d.γ b i j p) =
      (P.mulCoordinateCombination (fun k => normalFrameRelativeCoframeValue d.γ b k p)).angular (i,j) := by
    rw [hZero]
    exact (P.mulCoframe_angular d.γ b p i j).symm
  have hProd' := hProd.congr_deriv hVal
  have hFull := hProd'.add (hB.const_smul (nativePhysicalFirstCorrectionScalar d r0 b p))
  convert hFull using 1 <;> rfl

lemma nativePhysicalFirstCorrectionAngularFields_angular_eq {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} (d : Data) (h : Elliptic Ω K d.γ) (hK : 0 < K) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0)
    (hF : DifferentiableAt ℝ (nativePhysicalFirstCorrectionFamily d r0 b) (normalFrameRelativeNormalization d.γ p))
    (i j : I) :
    (nativePhysicalFirstCorrectionAngularFields d r0 b p).angular (i,j)=
      normalFrameRelativeAngularDerivative d.γ (nativePhysicalFirstCorrectionFamily d r0 b) i j p :=
  (hasDerivAt_nativeFirstCorrection_angular_curve hΩ d h hK r0 b p hp he i j).unique
    (hasDerivAt_relativeAngularFamily d.γ (nativePhysicalFirstCorrectionFamily d r0 b) p i j hF)

theorem nativePhysicalFirstCorrection_normalized_rotation_graph {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} (d : Data) (h : Elliptic Ω K d.γ) (hK : 0 < K) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0)
    (hF : DifferentiableAt ℝ (nativePhysicalFirstCorrectionFamily d r0 b) (normalFrameRelativeNormalization d.γ p))
    (i j : I) (u : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (nativePhysicalFirstCorrectionFamily d r0 b p
      (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (normalFrameRelativeAngularDerivative d.γ (nativePhysicalFirstCorrectionFamily d r0 b) i j p
          (sphereSobolevInclusionL 2 1 (by norm_num) u)+
          nativePhysicalFirstCorrectionFamily d r0 b p (sphereSobolevRotationL 2 i j u)) := by
  let P := firstCorrectionAngularPacket (normalizedFirstCorrectionCovector d.γ d.g₁ p)
    (fun k => normalFrameRelativeCoframeValue d.γ b k p) (nativePhysicalFirstCorrectionScalar d r0 b p)
  have hOp : P.operator=nativePhysicalFirstCorrectionFamily d r0 b p :=
    (congrArg CoarseAngularFields.operator (firstCorrectionAngularFields_ofPacket _ _ _)).trans
      (nativePhysicalFirstCorrectionAngularFields_operator d r0 b p)
  have hAngle : P.angular (i,j)=
      normalFrameRelativeAngularDerivative d.γ (nativePhysicalFirstCorrectionFamily d r0 b) i j p :=
    (congrArg (fun F : CoarseAngularFields => F.angular (i,j)) (firstCorrectionAngularFields_ofPacket _ _ _)).trans
      (nativePhysicalFirstCorrectionAngularFields_angular_eq hΩ d h hK r0 b p hp he hF i j)
  have hGraph := P.graph (i,j) u
  rw [hOp,hAngle] at hGraph
  exact hGraph

end ShrinkingSpheres
