import Proof.FullAdjointAngularNaturality
import Proof.RelativeCenterOneRotationDerivative
import Proof.ClosedGradientCurveDerivative
import Proof.NativeCenterGradientAngularFields
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

lemma NativeRelativeHorizontalTaylorData.hasDerivAt_centerGradient_angular_curve
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hpV : p ∈ V.domain) (hpC : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0)
    (i j : I) :
    HasDerivAt (fun θ => s.centerGradientAdjointFamily C (normalFrameRelativeAngularCurve d.γ p i j θ))
      ((s.centerGradientAngularFields C p).angular (i,j)) 0 := by
  let c := normalFrameRelativeAngularCurve d.γ p i j
  let P := s.response.fullAdjointAngularFields p
  let Q := fun k => (C k).closed p
  have hFix : normalFrameRelativeNormalization d.γ p=p := normalFrameRelativeNormalization_eq_self _ _ he
  have hZero : c 0=p := (normalFrameRelativeAngularCurve_zero d.γ p i j).trans hFix
  have hDaDiff : DifferentiableAt ℝ s.response.fullAdjoint (normalFrameRelativeNormalization d.γ p) :=
    (s.response.adjointSmooth.contDiffAt (s.response.domainOpen.mem_nhds
      (V.sub (V.normalizationStable p hpV)))).differentiableAt (by simp)
  have hDa := (hasDerivAt_relativeAngularFamily d.γ s.response.fullAdjoint p i j hDaDiff).congr_deriv
    (s.response.fullAdjointAngularFields_angular_eq V h hK (by norm_num) p hpV i j).symm
  have hQ (k : I) := RelativeCenterErrorCoefficientFamily.hasDerivAt_one_angular_curve_at C p hpC he k i j
  have hh := hasDerivAt_closedGradient_curve
    (fun θ k => (C k).closed (c θ)) (fun θ => s.response.fullAdjoint (c θ))
    (fun k => closedCoefficientAngularOneL i j (Q k)+
      (if k=i then closedOneBoundaryScalarMultiplierL (Q j) else 0)-
      (if k=j then closedOneBoundaryScalarMultiplierL (Q i) else 0))
    (P.angular (i,j)) 0 hQ hDa
  have hValue :
      ((∑ k : I,(coordinateGradientAdjointOperator (s.response.fullAdjoint (c 0)) k).comp
        (closedCoefficientAngularOneL i j (Q k)+
          (if k=i then closedOneBoundaryScalarMultiplierL (Q j) else 0)-
          (if k=j then closedOneBoundaryScalarMultiplierL (Q i) else 0)))+
        (P.angular (i,j)).comp (closedVectorNormalMultiplier (fun k => (C k).closed (c 0)))) =
      (CoarseAngularFields.gradient Q P).angular (i,j) := by
    simp only [hZero]
    have hP : P.operator=s.response.fullAdjoint p := s.response.fullAdjointAngularFields_operator p
    have hCoord (k : I) : coordinateGradientAdjointOperator (s.response.fullAdjoint p) k=
        (CoarseAngularFields.coordinateGradientAdjoint P k).operator :=
      (congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => coordinateGradientAdjointOperator A k) hP).symm
    have hSum :
        (∑ k : I,(coordinateGradientAdjointOperator (s.response.fullAdjoint p) k).comp
          (closedCoefficientAngularOneL i j (Q k)+
            (if k=i then closedOneBoundaryScalarMultiplierL (Q j) else 0)-
            (if k=j then closedOneBoundaryScalarMultiplierL (Q i) else 0))) =
        (∑ k : I,(CoarseAngularFields.coordinateGradientAdjoint P k).operator.comp
          (closedCoefficientAngularOneL i j (Q k)+
            (if k=i then closedOneBoundaryScalarMultiplierL (Q j) else 0)-
            (if k=j then closedOneBoundaryScalarMultiplierL (Q i) else 0))) :=
      Finset.sum_congr rfl (fun k _ => congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
        A.comp (closedCoefficientAngularOneL i j (Q k)+
          (if k=i then closedOneBoundaryScalarMultiplierL (Q j) else 0)-
          (if k=j then closedOneBoundaryScalarMultiplierL (Q i) else 0))) (hCoord k))
    exact (congrArg₂ (fun A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A+B) hSum rfl).trans
      (CoarseAngularFields.gradient_angular_vector_formula Q P i j).symm
  have hGradient := hh.congr_deriv hValue
  have hScaled := (hGradient.const_smul (normalFrameRelativeInverseRadiusFactor p)).const_smul (d.radius y)⁻¹
  have hFun (θ : ℝ) : s.centerGradientAdjointFamily C (c θ)=
      (d.radius y)⁻¹ • (normalFrameRelativeInverseRadiusFactor p •
        closedBoundaryGradientAdjoint (fun k => (C k).closed (c θ)) (s.response.fullAdjoint (c θ))) := rfl
  have hAngular : (d.radius y)⁻¹ • (normalFrameRelativeInverseRadiusFactor p •
      (CoarseAngularFields.gradient Q P).angular (i,j))=(s.centerGradientAngularFields C p).angular (i,j) := rfl
  exact (hScaled.congr_of_eventuallyEq (Filter.Eventually.of_forall hFun)).congr_deriv hAngular

lemma NativeRelativeHorizontalTaylorData.centerGradientAngularFields_angular_eq
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hpV : p ∈ V.domain) (hpC : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0)
    (hr : 1+p.2 ≠ 0) (i j : I) :
    (s.centerGradientAngularFields C p).angular (i,j) =
      normalFrameRelativeAngularDerivative d.γ (s.centerGradientAdjointFamily C) i j p := by
  have hFix : normalFrameRelativeNormalization d.γ p=p := normalFrameRelativeNormalization_eq_self _ _ he
  have hQ (k : I) : ContDiffAt ℝ ∞ (C k).closed p :=
    (contDiff_commonSupportClosedCoefficientFamily 3 (C k).scalar (C k).smooth
      (C k).support (C k).compact (C k).supported).contDiffAt
  have hDa : ContDiffAt ℝ ∞ s.response.fullAdjoint p :=
    s.response.adjointSmooth.contDiffAt (s.response.domainOpen.mem_nhds (V.sub hpV))
  have hG := contDiffAt_closedBoundaryGradientAdjoint (fun k => (C k).closed) s.response.fullAdjoint p hQ hDa
  have hR : ContDiffAt ℝ ∞ normalFrameRelativeInverseRadiusFactor p :=
    (contDiffAt_const.add contDiffAt_snd).inv hr
  have hF : DifferentiableAt ℝ (s.centerGradientAdjointFamily C) (normalFrameRelativeNormalization d.γ p) := by
    rw [hFix]
    exact ((hR.smul hG).const_smul (d.radius y)⁻¹).differentiableAt (by simp)
  exact (s.hasDerivAt_centerGradient_angular_curve C V h hK p hpV hpC he i j).unique
    (hasDerivAt_relativeAngularFamily d.γ (s.centerGradientAdjointFamily C) p i j hF)
end ShrinkingSpheres
