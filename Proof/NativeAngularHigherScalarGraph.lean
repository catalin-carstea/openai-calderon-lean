import Proof.UniformNativeAdjointHalfScalarNeighborhoodData
import Proof.NativeTaylorRotationHigherEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
/-- A scalar commutator identity valid as a germ can be differentiated
through its fixed multipliers and genuine domain inclusion. -/
lemma scalar_commutator_germ_fderiv
    {P0 E F : Type*} [NormedAddCommGroup P0] [NormedSpace ℝ P0]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : P0 → E →L[ℝ] F) (B : P0 → F →L[ℝ] F)
    (Mh : E →L[ℝ] E) (M : F →L[ℝ] F) (Inc : E →L[ℝ] F) (p v : P0)
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p)
    (hGerm : (fun q => (A q).comp Mh-M.comp (A q)) =ᶠ[𝓝 p]
      (fun q => (B q).comp Inc)) :
    (fderiv ℝ A p v).comp Mh-M.comp (fderiv ℝ A p v)=
      (fderiv ℝ B p v).comp Inc := by
  have hL := (hA.hasFDerivAt.clm_comp (hasFDerivAt_const Mh p)).sub
    ((hasFDerivAt_const M p).clm_comp hA.hasFDerivAt)
  have hR := hB.hasFDerivAt.clm_comp (hasFDerivAt_const Inc p)
  have hEq : fderiv ℝ (fun q => (A q).comp Mh-M.comp (A q)) p=
      fderiv ℝ (fun q => (B q).comp Inc) p := hGerm.fderiv_eq
  have hh := DFunLike.congr_fun (hL.fderiv.symm.trans (hEq.trans hR.fderiv)) v
  simpa only [_root_.add_apply,_root_.sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,_root_.zero_apply,
    ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,zero_add,add_zero] using hh

namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- Differentiation is justified by the SAME physical identity on the
recorded open neighborhood, rather than by a pointwise extension. -/
lemma angularHigherTaylor_scalar_graph
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ) (hΩ : IsOpen Ω)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (Q : ClosedCoefficientJets 3) (i j : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (A.domain.adjointRotationHigherFamily h hK (by norm_num) i j p).comp
      (closedThreeJetHigherScalarMultiplierL Q)-
    (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp
      (A.domain.adjointRotationHigherFamily h hK (by norm_num) i j p)=
    (normalFrameRelativeAngularDerivative d.γ
      (fun q => s.response.adjointHalfScalarCommutator F0 A.kernel Q q) i j p).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let P := A.domain.adjointHigherTaylor h hK (by norm_num)
  let C := fun q => s.response.adjointHalfScalarCommutator F0 A.kernel Q q
  let Mh := closedThreeJetHigherScalarMultiplierL Q
  let M := closedThreeJetHalfBoundaryScalarMultiplierL Q
  let Inc := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hP : DifferentiableAt ℝ P p :=
    ((A.domain.contDiffOn_adjointHigherTaylor hΩ h hK (by norm_num)).contDiffAt
      (A.domain.domainOpen.mem_nhds A.domain.pointMem)).differentiableAt (by simp)
  have hC : DifferentiableAt ℝ C p :=
    (A.scalar_jets (fun _ => Q) ‖Q‖ (SmoothFiniteJetBound.constant Q p 3)).smooth.differentiableAt (by simp)
  have hGerm : (fun q => (P q).comp Mh-M.comp (P q)) =ᶠ[𝓝 p]
      (fun q => (C q).comp Inc) := by
    filter_upwards [A.neighborhoodOpen.mem_nhds A.pointMem] with q hq
    exact A.high_graph q hq Q
  have hh := scalar_commutator_germ_fderiv P C Mh M Inc p
    (normalFrameRelativeAngularTangent d.γ p i j) hP hC hGerm
  simpa only [_root_.add_apply,_root_.sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,_root_.zero_apply,
    ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,zero_add,add_zero,
    P,C,Mh,M,Inc,p,NormalFrameRelativeResponsePacket.SymmetricAdjointDomain.adjointRotationHigherFamily,
    normalFrameRelativeAngularDerivative,normalFrameRelativeNormalization_eq_self d.γ ((y,frameVectorLinear d.frame y),0) he] using hh
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
