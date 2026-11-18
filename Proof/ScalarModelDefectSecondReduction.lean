import Proof.ModelAdjointDefectSectionApplication
import Proof.OneSectionCovariantInner
import Proof.SupportedCovariantSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms

def modelAdjointDefectDerivativeSection (d : Data) (U : X → SphereSobolev 2) (y b : X) : SphereSobolev 0 :=
  modelAdjointDefectFirstCoarseL d b y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
    modelAdjointDefectCoarseL d y (highSectionCovariantDerivative d U y b)

def scalarModelDefectSecondDensity (d : Data) (q : X → ℝ)
    (U : X → SphereSobolev 2) (V : X → SphereSobolev 3) (a b x : X) : ℝ :=
  q x*⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (U x)),
    oneSectionCovariantDerivative d (fun y => highSectionCovariantDerivative d
      (fun z => modelAdjointDefectSobolevL 3 d z (V z)) y b) x a⟫_ℝ

def scalarModelDefectSecondRemainder (d : Data) (q : X → ℝ)
    (U : X → SphereSobolev 2) (a b x : X) : ℝ :=
  -q x*⟪sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U x a),
    modelAdjointDefectDerivativeSection d U x b⟫_ℝ-
  fderiv ℝ q x a*⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (U x)),
    modelAdjointDefectDerivativeSection d U x b⟫_ℝ

/-- One genuine covariant Green identity for the actual scalar principal
operator applied to the SAME model defect. H3 and H2 source sections are
related by an explicit genuine inclusion; only original local geometry is used. -/
theorem scalar_model_defect_second_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (q : X → ℝ) (U : X → SphereSobolev 2) (V : X → SphereSobolev 3)
    (hCompat : ∀ x,sphereSobolevInclusionL 3 2 (by norm_num) (V x)=U x)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hq : ∀ x ∈ S,ContDiffAt ℝ ∞ q x)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) (a b : X) :
    Integrable (scalarModelDefectSecondDensity d q U V a b) ∧
      Integrable (scalarModelDefectSecondRemainder d q U a b) ∧
      (∫ x,scalarModelDefectSecondDensity d q U V a b x)=
        ∫ x,scalarModelDefectSecondRemainder d q U a b x := by
  let I21 := sphereSobolevInclusionL 2 1 (by norm_num)
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let W := fun x => modelAdjointDefectSobolevL 3 d x (V x)
  let Hb := fun x => highSectionCovariantDerivative d W x b
  let Hab := fun x => oneSectionCovariantDerivative d Hb x a
  let T := scalarModelDefectSecondDensity d q U V a b
  let R := scalarModelDefectSecondRemainder d q U a b
  let U1 := fun x => I21 (U x)
  let G := oneSectionCovariantInnerDensity d q U1 Hb a
  have hW := contDiff_supported_modelAdjointDefectSobolevL_apply hY 3 d hlog he V hV S hS.isClosed hSY h0V
  have hHb := contDiff_supported_highSectionCovariantDerivative hY d hg hK he W hW.1 S hS.isClosed hSY hW.2 b
  have hHab := contDiff_supported_oneSectionCovariantDerivative hY d hg hK he Hb hHb.1 S hS.isClosed hSY hHb.2 a
  have hU1 : ContDiff ℝ ∞ U1 := I21.contDiff.comp hU
  have h0U1 (x : X) (hx : x ∉ S) : U1 x=0 := by dsimp only [U1];rw [h0U x hx,map_zero]
  have hData := oneSectionCovariantDerivative_weighted_inner_data d q U1 Hb S hS hq hU1 hHb.1 h0U1 hHb.2 a
  have hGrad (x : X) : oneSectionCovariantDerivative d U1 x a=I10 (highSectionCovariantDerivative d U x a) :=
    oneSectionCovariantDerivative_high_inclusion d U x a (hU.differentiable (by simp) x)
  have hPoint (x : X) : R x=T x-G x := by
    by_cases hx : x ∈ S
    · have hZ := highSectionCovariantDerivative_modelAdjointDefect_three_coarse hY d hg hK he hFrame hlog
        U V hCompat (hSY hx) (hU.differentiable (by simp) x) (hV.differentiable (by simp) x) b
      simp only [R,T,G,scalarModelDefectSecondRemainder,scalarModelDefectSecondDensity,
        oneSectionCovariantInnerDensity,hGrad,Hb,W,I10,I21,modelAdjointDefectDerivativeSection,hZ]
      ring
    · have hDU := highSectionCovariantDerivative_zero_off d U S hS.isClosed h0U a x hx
      have hDU1 := oneSectionCovariantDerivative_zero_off d U1 S hS.isClosed h0U1 a x hx
      simp only [R,T,G,scalarModelDefectSecondRemainder,scalarModelDefectSecondDensity,
        oneSectionCovariantInnerDensity,h0U x hx,h0U1 x hx,hDU,hDU1,map_zero,
        inner_zero_left,mul_zero,neg_zero,sub_zero,zero_sub,add_zero,zero_add]
  have hT : Integrable T := integrable_local_weighted_operator_pair (innerSL ℝ) q
    (fun x => I10 (I21 (U x))) Hab (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0))
    S hS hq (I10.contDiff.comp hU1) hHab.1 hHab.2 (fun _ _ => contDiffAt_const)
  have hG : Integrable G := hData.1
  have hR : Integrable R := (hT.sub hG).congr (Eventually.of_forall (fun x => (hPoint x).symm))
  refine ⟨hT,hR,?_⟩
  symm
  calc
    _ = ∫ x,T x-G x := integral_congr_ae (Eventually.of_forall hPoint)
    _ = (∫ x,T x)-(∫ x,G x) := integral_sub hT hG
    _ = _ := by rw [hData.2,sub_zero]

lemma scalarModelDefectSecondDensity_zero_off (d : Data) (q : X → ℝ)
    (U : X → SphereSobolev 2) (V : X → SphereSobolev 3) (a b x : X) (h0 : U x=0) :
    scalarModelDefectSecondDensity d q U V a b x=0 := by
  simp only [scalarModelDefectSecondDensity,h0,map_zero,inner_zero_left,mul_zero]

lemma scalarModelDefectSecondRemainder_zero_off (d : Data) (q : X → ℝ)
    (U : X → SphereSobolev 2) (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0)
    (a b x : X) (hx : x ∉ S) : scalarModelDefectSecondRemainder d q U a b x=0 := by
  simp only [scalarModelDefectSecondRemainder,h0 x hx,map_zero,
    highSectionCovariantDerivative_zero_off d U S hS h0 a x hx,inner_zero_left,mul_zero,neg_zero,sub_zero]

end ShrinkingSpheres
