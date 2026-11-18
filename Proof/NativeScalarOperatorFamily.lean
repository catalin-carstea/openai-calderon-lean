import Proof.UniformNativeAdjointHalfScalarNeighborhoodData
import Proof.LinearFamilyJetEvaluation
import Proof.NativeClosedMovingMultiplierSmoothness
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
lemma fderiv_clm_apply_const
    {P0 E F : Type*} [NormedAddCommGroup P0] [NormedSpace ℝ P0]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : P0 → E →L[ℝ] F) (p v : P0) (u : E) (hA : DifferentiableAt ℝ A p) :
    fderiv ℝ (fun q => A q u) p v=(fderiv ℝ A p v) u := by
  let ev : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F u
  exact DFunLike.congr_fun (ev.hasFDerivAt.comp p hA.hasFDerivAt).fderiv v

namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def scalarOperatorFamily (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (p : NormalFrameRelativeParameter) : ClosedCoefficientJets 3 →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  commonSupportNativeClosedMultiplierKernel s.coefficients.a s.coefficients.a1
    s.coefficients.smooth s.coefficients.firstSmooth s.coefficients.support s.coefficients.support
    s.coefficients.compact s.coefficients.compact s.coefficients.supported s.coefficients.firstSupported
    F0 (d.radius y) p+
  ((ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) (SphereSobolev (1/2:ℝ))
    (SphereSobolev (1/2:ℝ))) (-(A.kernel p).adjoint)).comp closedThreeJetHalfBoundaryScalarMultiplierL-
  ((ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) (SphereSobolev (1/2:ℝ))
    (SphereSobolev (1/2:ℝ))).flip (-(A.kernel p).adjoint)).comp closedThreeJetHalfBoundaryScalarMultiplierL

lemma scalarOperatorFamily_apply (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (p : NormalFrameRelativeParameter) (Q : ClosedCoefficientJets 3) :
    A.scalarOperatorFamily p Q=s.response.adjointHalfScalarCommutator F0 A.kernel Q p := by
  rfl

lemma scalarOperatorFamily_smooth (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ) :
    ContDiffAt ℝ ∞ A.scalarOperatorFamily ((y,frameVectorLinear d.frame y),0) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hG := contDiffAt_commonSupportNativeClosedMultiplierKernel
    s.coefficients.a s.coefficients.a1 s.coefficients.smooth s.coefficients.firstSmooth
    s.coefficients.support s.coefficients.support s.coefficients.compact s.coefficients.compact
    s.coefficients.supported s.coefficients.firstSupported F0 (d.radius y) p s.point.strong s.point.weak
  have hK : ContDiffAt ℝ ∞ (fun q => (-(A.kernel q).adjoint :
      SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))) p := A.kernel_jets.adjoint.neg.smooth
  let Comp := ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) (SphereSobolev (1/2:ℝ))
    (SphereSobolev (1/2:ℝ))
  have hLeft := (Comp.contDiff.contDiffAt.comp p hK).clm_comp
    (contDiffAt_const (c:=closedThreeJetHalfBoundaryScalarMultiplierL))
  have hRight := (Comp.flip.contDiff.contDiffAt.comp p hK).clm_comp
    (contDiffAt_const (c:=closedThreeJetHalfBoundaryScalarMultiplierL))
  exact (hG.add hLeft).sub hRight

/-- The already checked fixed-input estimates control the SAME scalar
operator family in operator norm, including every joint three-jet. -/
lemma scalarOperatorFamily_three_jets (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (hCJ : 0 ≤ CJ) :
    SmoothFiniteJetBound A.scalarOperatorFamily ((y,frameVectorLinear d.frame y),0) 3
      (CJ*(d.radius y)^2) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hS := A.scalarOperatorFamily_smooth
  refine ⟨mul_nonneg hCJ (sq_nonneg _),hS,?_⟩
  intro n hn
  apply norm_iteratedFDeriv_linear_family_of_apply_le _ p hS n _ (mul_nonneg hCJ (sq_nonneg _))
  intro Q
  have hh := (A.scalar_jets (fun _ => Q) ‖Q‖ (SmoothFiniteJetBound.constant Q p 3)).bound n hn
  simpa only [scalarOperatorFamily_apply] using hh.trans_eq (by ring)
/-- Fixed-coefficient evaluation commutes with the actual normalized
angular derivative of the SAME scalar operator family. -/
lemma scalarOperatorFamily_angular_apply
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q : ClosedCoefficientJets 3) (i j : I) :
    normalFrameRelativeAngularDerivative d.γ A.scalarOperatorFamily i j
      ((y,frameVectorLinear d.frame y),0) Q=
    normalFrameRelativeAngularDerivative d.γ
      (fun p => s.response.adjointHalfScalarCommutator F0 A.kernel Q p) i j
        ((y,frameVectorLinear d.frame y),0) := by
  have hh := fderiv_clm_apply_const A.scalarOperatorFamily ((y,frameVectorLinear d.frame y),0)
    (normalFrameRelativeAngularTangent d.γ ((y,frameVectorLinear d.frame y),0) i j) Q
    (A.scalarOperatorFamily_smooth.differentiableAt (by simp))
  simpa only [normalFrameRelativeAngularDerivative,
    normalFrameRelativeNormalization_eq_self d.γ ((y,frameVectorLinear d.frame y),0) he,
    scalarOperatorFamily_apply] using hh.symm
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
