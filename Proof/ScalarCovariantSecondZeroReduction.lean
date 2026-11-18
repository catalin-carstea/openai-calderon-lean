import Proof.OneSectionCovariantInner
import Proof.SupportedCovariantSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OperatorForms

def scalarCovariantSecondZeroDensity (d : Data) (q : X → ℝ) (U : X → SphereSobolev 2)
    (a b x : X) : ℝ :=
  q x*⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (U x)),
    oneSectionCovariantDerivative d (fun y => highSectionCovariantDerivative d U y b) x a⟫_ℝ

def scalarCovariantSecondZeroRemainder (d : Data) (q : X → ℝ) (U : X → SphereSobolev 2)
    (a b x : X) : ℝ :=
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num);
  -q x*⟪I10 (highSectionCovariantDerivative d U x a),I10 (highSectionCovariantDerivative d U x b)⟫_ℝ-
    fderiv ℝ q x a*⟪I10 (sphereSobolevInclusionL 2 1 (by norm_num) (U x)),
      I10 (highSectionCovariantDerivative d U x b)⟫_ℝ

/-- One genuine covariant Green identity removes the scalar second-base
derivative against the zero adjoint coefficient. -/
theorem scalar_covariant_second_zero_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : X → ℝ) (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hq : ∀ x ∈ S,ContDiffAt ℝ ∞ q x) (h0U : ∀ x ∉ S,U x=0) (a b : X) :
    Integrable (scalarCovariantSecondZeroDensity d q U a b) ∧
      Integrable (scalarCovariantSecondZeroRemainder d q U a b) ∧
      (∫ x,scalarCovariantSecondZeroDensity d q U a b x)=
        ∫ x,scalarCovariantSecondZeroRemainder d q U a b x := by
  let I21 := sphereSobolevInclusionL 2 1 (by norm_num)
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let Hb := fun x => highSectionCovariantDerivative d U x b
  let Hab := fun x => oneSectionCovariantDerivative d Hb x a
  let T := scalarCovariantSecondZeroDensity d q U a b
  let R := scalarCovariantSecondZeroRemainder d q U a b
  let G := oneSectionCovariantInnerDensity d q (fun x => I21 (U x)) Hb a
  have hHb := contDiff_supported_highSectionCovariantDerivative hY d hg hK he U hU S hS.isClosed hSY h0U b
  have hHab := contDiff_supported_oneSectionCovariantDerivative hY d hg hK he Hb hHb.1 S hS.isClosed hSY hHb.2 a
  have h0I (x : X) (hx : x ∉ S) : I21 (U x)=0 := by rw [h0U x hx,map_zero]
  have hData := oneSectionCovariantDerivative_weighted_inner_data d q (fun x => I21 (U x)) Hb
    S hS hq (I21.contDiff.comp hU) hHb.1 h0I hHb.2 a
  have hiG : Integrable G := hData.1
  have hzG : (∫ x,G x)=0 := hData.2
  have hGrad (x : X) : oneSectionCovariantDerivative d (fun y => I21 (U y)) x a=
      I10 (highSectionCovariantDerivative d U x a) :=
    oneSectionCovariantDerivative_high_inclusion d U x a (hU.differentiable (by simp) x)
  have hPoint (x : X) : R x=T x-G x := by
    simp only [R,T,G,scalarCovariantSecondZeroRemainder,scalarCovariantSecondZeroDensity,
      oneSectionCovariantInnerDensity,hGrad,Hb]
    ring
  have hT : Integrable T := by
    have ht := integrable_local_weighted_operator_pair (innerSL ℝ) q
      (fun x => I10 (I21 (U x))) Hab (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0))
      S hS hq (I10.contDiff.comp (I21.contDiff.comp hU)) hHab.1 hHab.2 (fun _ _ => contDiffAt_const)
    exact ht
  have hR : Integrable R := (hT.sub hiG).congr (Eventually.of_forall (fun x => (hPoint x).symm))
  refine ⟨hT,hR,?_⟩
  symm
  calc
    _ = ∫ x,T x-G x := integral_congr_ae (Eventually.of_forall hPoint)
    _ = (∫ x,T x)-(∫ x,G x) := integral_sub hT hiG
    _ = _ := by rw [hzG,sub_zero]

lemma scalarCovariantSecondZeroDensity_zero_off (d : Data) (q : X → ℝ) (U : X → SphereSobolev 2)
    (a b x : X) (h0 : U x=0) : scalarCovariantSecondZeroDensity d q U a b x=0 := by
  simp only [scalarCovariantSecondZeroDensity,h0,map_zero,inner_zero_left,mul_zero]

lemma scalarCovariantSecondZeroRemainder_zero_off (d : Data) (q : X → ℝ) (U : X → SphereSobolev 2)
    (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0) (a b x : X) (hx : x ∉ S) :
    scalarCovariantSecondZeroRemainder d q U a b x=0 := by
  simp only [scalarCovariantSecondZeroRemainder,
    highSectionCovariantDerivative_zero_off d U S hS h0 a x hx,
    highSectionCovariantDerivative_zero_off d U S hS h0 b x hx,
    map_zero,inner_zero_left,inner_zero_right,mul_zero,sub_zero,neg_zero]

end ShrinkingSpheres
