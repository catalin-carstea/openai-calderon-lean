import Proof.CovariantSecondTripleIdentity
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
open OperatorForms

lemma scalar_third_cross_packed_algebra {E A : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : A → E) (H R : A → A → E)
    (hR : ∀ v w,H v w-H w v=R v w) (a b c : A) (q qa qb qc : ℝ) :
    -qa*⟪V b,V c⟫_ℝ-qb*⟪V a,V c⟫_ℝ+qc*⟪V a,V b⟫_ℝ+
      q*⟪R a b,V c⟫_ℝ+q*⟪R c b,V a⟫_ℝ-q*⟪R a c,V b⟫_ℝ=
    2*(q*⟪H a b,V c⟫_ℝ)-
      (q*(⟪V b,H a c⟫_ℝ+⟪H a b,V c⟫_ℝ)+qa*⟪V b,V c⟫_ℝ)-
      (q*(⟪V a,H b c⟫_ℝ+⟪H b a,V c⟫_ℝ)+qb*⟪V a,V c⟫_ℝ)+
      (q*(⟪V a,H c b⟫_ℝ+⟪H c a,V b⟫_ℝ)+qc*⟪V a,V b⟫_ℝ) := by
  have h := inner_covariant_second_triple_algebra V H R hR a b c
  linear_combination -q*h

def scalarCovariantThirdCrossDensity (d : Data) (q : X → ℝ) (U : X → SphereSobolev 2)
    (a b c x : X) : ℝ :=
  q x*⟪oneSectionCovariantDerivative d (fun y => highSectionCovariantDerivative d U y b) x a,
    sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U x c)⟫_ℝ

def scalarCovariantThirdCrossRemainder (d : Data) (q : X → ℝ) (U : X → SphereSobolev 2)
    (a b c x : X) : ℝ :=
  let V := fun v => sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U x v)
  let IU := sphereSobolevInclusionL 2 1 (by norm_num) (U x);
  -(fderiv ℝ q x a) * ⟪V b,V c⟫_ℝ - (fderiv ℝ q x b) * ⟪V a,V c⟫_ℝ +
    (fderiv ℝ q x c) * ⟪V a,V b⟫_ℝ +
    q x * ⟪frameCurvatureRotationL d.γ d.frame x a b IU,V c⟫_ℝ +
    q x * ⟪frameCurvatureRotationL d.γ d.frame x c b IU,V a⟫_ℝ -
    q x * ⟪frameCurvatureRotationL d.γ d.frame x a c IU,V b⟫_ℝ

/-- Integrated third-base scalar cross reduction with integrability. The
remainder has only products of first section derivatives and the actual
first-order curvature action; curvature is never differentiated. -/
theorem scalar_covariant_third_cross_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (q : X → ℝ) (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hq : ∀ x ∈ S,ContDiffAt ℝ ∞ q x) (h0U : ∀ x ∉ S,U x=0) (a b c : X) :
    Integrable (scalarCovariantThirdCrossDensity d q U a b c) ∧
      Integrable (scalarCovariantThirdCrossRemainder d q U a b c) ∧
      2*(∫ x,scalarCovariantThirdCrossDensity d q U a b c x)=
        ∫ x,scalarCovariantThirdCrossRemainder d q U a b c x := by
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let H := fun v x => highSectionCovariantDerivative d U x v
  let T := scalarCovariantThirdCrossDensity d q U a b c
  let R := scalarCovariantThirdCrossRemainder d q U a b c
  have hHD (v : X) := contDiff_supported_highSectionCovariantDerivative hY d hg hK he U hU
    S hS.isClosed hSY h0U v
  have hH2D (v w : X) := contDiff_supported_oneSectionCovariantDerivative hY d hg hK he (H w)
    (hHD w).1 S hS.isClosed hSY (hHD w).2 v
  let G1 := oneSectionCovariantInnerDensity d q (H b) (H c) a
  let G2 := oneSectionCovariantInnerDensity d q (H a) (H c) b
  let G3 := oneSectionCovariantInnerDensity d q (H a) (H b) c
  have hG1 := oneSectionCovariantDerivative_weighted_inner_data d q (H b) (H c) S hS hq
    (hHD b).1 (hHD c).1 (hHD b).2 (hHD c).2 a
  have hG2 := oneSectionCovariantDerivative_weighted_inner_data d q (H a) (H c) S hS hq
    (hHD a).1 (hHD c).1 (hHD a).2 (hHD c).2 b
  have hG3 := oneSectionCovariantDerivative_weighted_inner_data d q (H a) (H b) S hS hq
    (hHD a).1 (hHD b).1 (hHD a).2 (hHD b).2 c
  have hPoint (x : X) : R x=2*T x-G1 x-G2 x+G3 x := by
    by_cases hx : x ∈ S
    · exact scalar_third_cross_packed_algebra (fun v => I10 (H v x))
        (fun v w => oneSectionCovariantDerivative d (H w) x v)
        (fun v w => frameCurvatureRotationL d.γ d.frame x v w
          (sphereSobolevInclusionL 2 1 (by norm_num) (U x)))
        (fun v w => hg.highSectionCovariantDerivative_commutator hY d hK he hFrame U hU.contDiffOn
          (hSY hx) v w) a b c (q x) (fderiv ℝ q x a) (fderiv ℝ q x b) (fderiv ℝ q x c)
    · have hH0 (v : X) : H v x=0 := (hHD v).2 x hx
      have hH20 (v w : X) : oneSectionCovariantDerivative d (H w) x v=0 := (hH2D v w).2 x hx
      simp only [R,T,scalarCovariantThirdCrossRemainder,scalarCovariantThirdCrossDensity,
        G1,G2,G3,oneSectionCovariantInnerDensity,H,hH0,hH20,h0U x hx,map_zero,
        inner_zero_left,inner_zero_right,mul_zero,add_zero,sub_zero,zero_sub,neg_zero]
  have hT : Integrable T := by
    have ht := integrable_local_weighted_operator_pair (innerSL ℝ) q
      (fun x => oneSectionCovariantDerivative d (H b) x a) (fun x => I10 (H c x))
      (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0)) S hS hq (hH2D a b).1
      (I10.contDiff.comp (hHD c).1) (fun x hx => by
        change I10 (highSectionCovariantDerivative d U x c)=0
        rw [(hHD c).2 x hx,map_zero])
      (fun _ _ => contDiffAt_const)
    exact ht
  have hR : Integrable R :=
    ((((hT.const_mul 2).sub hG1.1).sub hG2.1).add hG3.1).congr
      (Eventually.of_forall (fun x => (hPoint x).symm))
  have hi1 : Integrable G1 := hG1.1
  have hi2 : Integrable G2 := hG2.1
  have hi3 : Integrable G3 := hG3.1
  have hz1 : (∫ x,G1 x)=0 := hG1.2
  have hz2 : (∫ x,G2 x)=0 := hG2.2
  have hz3 : (∫ x,G3 x)=0 := hG3.2
  have hIntegral : (∫ x,R x)=2*(∫ x,T x) := by
    calc
      _ = ∫ x,2*T x-G1 x-G2 x+G3 x := integral_congr_ae (Eventually.of_forall hPoint)
      _ = (∫ x,2*T x-G1 x-G2 x)+(∫ x,G3 x) :=
        integral_add (((hT.const_mul 2).sub hi1).sub hi2) hi3
      _ = ((∫ x,2*T x)-(∫ x,G1 x)-(∫ x,G2 x))+(∫ x,G3 x) := by
        calc
          _ = ((∫ x,2*T x-G1 x)-(∫ x,G2 x))+(∫ x,G3 x) :=
            congrArg (fun r : ℝ => r+(∫ x,G3 x)) (integral_sub ((hT.const_mul 2).sub hi1) hi2)
          _ = _ := congrArg (fun r : ℝ => r-(∫ x,G2 x)+(∫ x,G3 x))
            (integral_sub (hT.const_mul 2) hi1)
      _ = _ := by rw [integral_const_mul,hz1,hz2,hz3];ring
  exact ⟨hT,hR,hIntegral.symm⟩

end ShrinkingSpheres
