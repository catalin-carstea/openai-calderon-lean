import Proof.OneSectionCovariantInner
import Proof.CovariantScalarSectionProduct
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
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.PrincipalCommutator OperatorForms

/-- Genuine double covariant integration by parts for one real scalar
second-order coefficient. The connection is kept in both derivatives. -/
theorem scalar_covariant_second_term_green_data {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : X → ℝ) (U V : X → SphereSobolev 2)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hq : ∀ x ∈ S,ContDiffAt ℝ ∞ q x)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) (a b : X) :
    let L := fun x => q x*⟪oneSectionCovariantDerivative d
        (fun y => highSectionCovariantDerivative d U y b) x a,
      sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (V x))⟫_ℝ
    let R := fun x => ⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (U x)),
      oneSectionCovariantDerivative d
        (fun y => highSectionCovariantDerivative d (fun z => q z • V z) y a) x b⟫_ℝ
    Integrable L ∧ Integrable R ∧ (∫ x,L x)=(∫ x,R x) := by
  let I21 := sphereSobolevInclusionL 2 1 (by norm_num)
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let I20 := I10.comp I21
  let W := fun x => q x • V x
  let Ub := fun x => highSectionCovariantDerivative d U x b
  let Wa := fun x => highSectionCovariantDerivative d W x a
  let Uab := fun x => oneSectionCovariantDerivative d Ub x a
  let Wba := fun x => oneSectionCovariantDerivative d Wa x b
  have hWS : ContDiff ℝ ∞ W := contDiff_supported_smul q V S hS.isClosed hV h0V hq
  have h0W (x : X) (hx : x ∉ S) : W x=0 := by simp only [W,h0V x hx,smul_zero]
  have hUb := contDiff_supported_highSectionCovariantDerivative hY d hg hK he U hU S hS.isClosed hSY h0U b
  have hWa := contDiff_supported_highSectionCovariantDerivative hY d hg hK he W hWS S hS.isClosed hSY h0W a
  have hUab := contDiff_supported_oneSectionCovariantDerivative hY d hg hK he Ub hUb.1 S hS.isClosed hSY hUb.2 a
  have hWba := contDiff_supported_oneSectionCovariantDerivative hY d hg hK he Wa hWa.1 S hS.isClosed hSY hWa.2 b
  have hIU := I21.contDiff.comp hU
  have hIV := I21.contDiff.comp hV
  have h0IU (x : X) (hx : x ∉ S) : I21 (U x)=0 := by rw [h0U x hx,map_zero]
  have h0IV (x : X) (hx : x ∉ S) : I21 (V x)=0 := by rw [h0V x hx,map_zero]
  let G1 := oneSectionCovariantInnerDensity d q Ub (fun x => I21 (V x)) a
  let G2 := oneSectionCovariantInnerDensity d (fun _ => (1:ℝ)) (fun x => I21 (U x)) Wa b
  have hG1 := oneSectionCovariantDerivative_weighted_inner_data d q Ub (fun x => I21 (V x))
    S hS hq hUb.1 hIV hUb.2 h0IV a
  have hG2 := oneSectionCovariantDerivative_weighted_inner_data d (fun _ => (1:ℝ))
    (fun x => I21 (U x)) Wa S hS (fun _ _ => contDiffAt_const) hIU hWa.1 h0IU hWa.2 b
  have hWProd (x : X) : Wa x=fderiv ℝ q x a • I21 (V x)+q x • highSectionCovariantDerivative d V x a := by
    by_cases hx : x ∈ S
    · exact highSectionCovariantDerivative_smul d q V x a
        ((hq x hx).differentiableAt (by simp)) (hV.differentiable (by simp) x)
    · change highSectionCovariantDerivative d W x a= _
      rw [hWa.2 x hx,h0V x hx,map_zero,smul_zero,
        highSectionCovariantDerivative_zero_off d V S hS.isClosed h0V a x hx,smul_zero,add_zero]
  have hDV (x : X) : oneSectionCovariantDerivative d (fun z => I21 (V z)) x a=
      I10 (highSectionCovariantDerivative d V x a) :=
    oneSectionCovariantDerivative_high_inclusion d V x a (hV.differentiable (by simp) x)
  have hDU (x : X) : oneSectionCovariantDerivative d (fun z => I21 (U z)) x b=I10 (Ub x) :=
    oneSectionCovariantDerivative_high_inclusion d U x b (hU.differentiable (by simp) x)
  have hDOne (x : X) : fderiv ℝ (fun _ : X => (1:ℝ)) x b=0 :=
    DFunLike.congr_fun (hasFDerivAt_const (1:ℝ) x).fderiv b
  let L := fun x => q x*⟪Uab x,I20 (V x)⟫_ℝ
  let R := fun x => ⟪I20 (U x),Wba x⟫_ℝ
  have hPoint (x : X) : G1 x-G2 x=L x-R x := by
    simp only [G1,G2,oneSectionCovariantInnerDensity,hDV,hDU,hDOne,hWProd,
      map_add,map_smul,inner_add_right,inner_smul_right,mul_zero,zero_mul,one_mul,add_zero,
      Uab,Wba,L,R,I20,ContinuousLinearMap.comp_apply]
    ring
  have hPacked : (∫ x,L x-R x)=0 := by
    calc
      _ = ∫ x,G1 x-G2 x := integral_congr_ae (Eventually.of_forall (fun x => (hPoint x).symm))
      _ = (∫ x,G1 x)-(∫ x,G2 x) := integral_sub hG1.1 hG2.1
      _ = 0 := by rw [hG1.2,hG2.2];ring
  have h0IV0 (x : X) (hx : x ∉ S) : I20 (V x)=0 := by rw [h0V x hx,map_zero]
  have hL : Integrable L := integrable_local_weighted_operator_pair (innerSL ℝ) q Uab
    (fun x => I20 (V x)) (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0)) S hS hq
    hUab.1 (I20.contDiff.comp hV) h0IV0 (fun _ _ => contDiffAt_const)
  have hR : Integrable R := by
    have ht := integrable_local_weighted_operator_pair (innerSL ℝ) (fun _ => (1:ℝ))
      (fun x => I20 (U x)) Wba (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0))
      S hS (fun _ _ => contDiffAt_const) (I20.contDiff.comp hU) hWba.1 hWba.2
      (fun _ _ => contDiffAt_const)
    change Integrable (fun x => (1:ℝ)*⟪I20 (U x),Wba x⟫_ℝ) at ht
    simpa only [one_mul,R] using ht
  rw [integral_sub hL hR] at hPacked
  exact ⟨hL,hR,sub_eq_zero.mp hPacked⟩

theorem scalar_covariant_second_term_green {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : X → ℝ) (U V : X → SphereSobolev 2)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hq : ∀ x ∈ S,ContDiffAt ℝ ∞ q x)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) (a b : X) :
    (∫ x,q x*⟪oneSectionCovariantDerivative d
        (fun y => highSectionCovariantDerivative d U y b) x a,
      sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (V x))⟫_ℝ)=
    ∫ x,⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (U x)),
      oneSectionCovariantDerivative d
        (fun y => highSectionCovariantDerivative d (fun z => q z • V z) y a) x b⟫_ℝ :=
  (scalar_covariant_second_term_green_data hY d hg hK he q U V S hS hSY hq hU hV h0U h0V a b).2.2

end ShrinkingSpheres
