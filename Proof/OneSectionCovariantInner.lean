import Proof.OneSectionCovariantDerivative
import Proof.LocalMixedOperatorGreen

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.PrincipalCommutator
open OperatorForms

def oneSectionAngularConnectionL (d : Data) (y a : X) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL 1 i j

lemma oneSectionCovariantDerivative_eq_connection (d : Data) (U : X → SphereSobolev 1) (y a : X) :
    oneSectionCovariantDerivative d U y a=
      sphereSobolevInclusionL 1 0 (by norm_num) (fderiv ℝ U y a)-
        oneSectionAngularConnectionL d y a (U y) := by
  simp only [oneSectionCovariantDerivative,oneSectionAngularConnectionL,_root_.sum_apply,_root_.smul_apply]

lemma oneSectionAngularConnectionL_skew (d : Data) (y a : X) (u v : SphereSobolev 1) :
    ⟪oneSectionAngularConnectionL d y a u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      -⟪sphereSobolevInclusionL 1 0 (by norm_num) u,oneSectionAngularConnectionL d y a v⟫_ℝ := by
  simp only [oneSectionAngularConnectionL,_root_.sum_apply,_root_.smul_apply,
    sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    orderOneRotation_skew,inner_neg_right,mul_neg,Finset.sum_neg_distrib]

/-- Metric compatibility of the actual angular connection on genuine
H1 sections. This cancellation does not bound the frame connection. -/
lemma oneSectionCovariantDerivative_inner_sum (d : Data) (U V : X → SphereSobolev 1) (y a : X) :
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) (U y),oneSectionCovariantDerivative d V y a⟫_ℝ+
      ⟪oneSectionCovariantDerivative d U y a,sphereSobolevInclusionL 1 0 (by norm_num) (V y)⟫_ℝ=
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) (U y),
      sphereSobolevInclusionL 1 0 (by norm_num) (fderiv ℝ V y a)⟫_ℝ+
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) (fderiv ℝ U y a),
        sphereSobolevInclusionL 1 0 (by norm_num) (V y)⟫_ℝ := by
  rw [oneSectionCovariantDerivative_eq_connection,oneSectionCovariantDerivative_eq_connection,
    inner_sub_right,inner_sub_left,oneSectionAngularConnectionL_skew]
  ring

def oneSectionCovariantInnerDensity (d : Data) (q : X → ℝ) (U V : X → SphereSobolev 1)
    (a x : X) : ℝ :=
  q x*(⟪sphereSobolevInclusionL 1 0 (by norm_num) (U x),oneSectionCovariantDerivative d V x a⟫_ℝ+
    ⟪oneSectionCovariantDerivative d U x a,sphereSobolevInclusionL 1 0 (by norm_num) (V x)⟫_ℝ)+
    fderiv ℝ q x a*⟪sphereSobolevInclusionL 1 0 (by norm_num) (U x),
      sphereSobolevInclusionL 1 0 (by norm_num) (V x)⟫_ℝ

/-- Packed covariant integration by parts and integrability on supported
genuine H1 sections, with a local smooth weight and no frame jet budget. -/
theorem oneSectionCovariantDerivative_weighted_inner_data
    (d : Data) (q : X → ℝ) (U V : X → SphereSobolev 1)
    (S : Set X) (hS : IsCompact S) (hq : ∀ x ∈ S,ContDiffAt ℝ ∞ q x)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) (a : X) :
    Integrable (oneSectionCovariantInnerDensity d q U V a) ∧
      (∫ x,oneSectionCovariantInnerDensity d q U V a x)=0 := by
  let I10 := sphereSobolevInclusionL 1 0 (by norm_num)
  let f0 := fun x => q x*⟪I10 (U x),I10 (directionalFDeriv a V x)⟫_ℝ
  let f1 := fun x => directionalFDeriv a q x*⟪I10 (U x),I10 (V x)⟫_ℝ+
    q x*⟪I10 (directionalFDeriv a U x),I10 (V x)⟫_ℝ
  have hRaw := OperatorForms.weighted_first_operator_green_mixed_local
    (innerSL ℝ) I10 q U V (fun _ => I10) S hS hq hU hV h0U h0V
    (fun _ _ => contDiffAt_const) a
  have hDConst (x : X) : directionalFDeriv a (fun _ : X => I10) x=0 := by
    exact DFunLike.congr_fun (hasFDerivAt_const I10 x).fderiv a
  change (∫ x,q x*⟪I10 (U x),I10 (directionalFDeriv a V x)⟫_ℝ)=
    -(∫ x,directionalFDeriv a q x*⟪I10 (U x),I10 (V x)⟫_ℝ+
      q x*⟪I10 (directionalFDeriv a U x),I10 (V x)⟫_ℝ+
      q x*⟪I10 (U x),directionalFDeriv a (fun _ => I10) x (V x)⟫_ℝ) at hRaw
  simp only [hDConst,_root_.zero_apply,inner_zero_right,mul_zero,add_zero] at hRaw
  have hG : (∫ x,f0 x)=-(∫ x,f1 x) := hRaw
  have h0VD (x : X) (hx : x ∉ S) : directionalFDeriv a V x=0 :=
    directional_eq_zero_off V S hS.isClosed h0V a x hx
  have hf0 : Integrable f0 := OperatorForms.integrable_local_weighted_operator_pair
    (innerSL ℝ) q (fun x => I10 (U x)) (directionalFDeriv a V) (fun _ => I10)
    S hS hq (I10.contDiff.comp hU) (contDiff_directionalFDeriv a V hV) h0VD
    (fun _ _ => contDiffAt_const)
  have hf1a : Integrable (fun x => directionalFDeriv a q x*⟪I10 (U x),I10 (V x)⟫_ℝ) :=
    OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) (directionalFDeriv a q)
      (fun x => I10 (U x)) V (fun _ => I10) S hS
      (fun x hx => contDiffAt_directional q x a (hq x hx))
      (I10.contDiff.comp hU) hV h0V (fun _ _ => contDiffAt_const)
  have hf1b : Integrable (fun x => q x*⟪I10 (directionalFDeriv a U x),I10 (V x)⟫_ℝ) :=
    OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) q
      (fun x => I10 (directionalFDeriv a U x)) V (fun _ => I10) S hS hq
      (I10.contDiff.comp (contDiff_directionalFDeriv a U hU)) hV h0V (fun _ _ => contDiffAt_const)
  have hPoint (x : X) : q x*(⟪I10 (U x),oneSectionCovariantDerivative d V x a⟫_ℝ+
      ⟪oneSectionCovariantDerivative d U x a,I10 (V x)⟫_ℝ)+
        fderiv ℝ q x a*⟪I10 (U x),I10 (V x)⟫_ℝ=f0 x+f1 x := by
    rw [oneSectionCovariantDerivative_inner_sum]
    dsimp only [f0,f1,I10,directionalFDeriv]
    ring
  have hf1 : Integrable f1 := by
    have ht := hf1a.add hf1b
    change Integrable f1 at ht
    exact ht
  have hEq (x : X) : oneSectionCovariantInnerDensity d q U V a x=f0 x+f1 x := hPoint x
  refine ⟨(hf0.add hf1).congr (Eventually.of_forall (fun x => (hEq x).symm)),?_⟩
  calc
    (∫ x,oneSectionCovariantInnerDensity d q U V a x)=(∫ x,f0 x+f1 x) :=
      integral_congr_ae (Eventually.of_forall hEq)
    _ = (∫ x,f0 x)+(∫ x,f1 x) := integral_add hf0 hf1
    _ = 0 := by rw [hG];exact neg_add_cancel _

theorem oneSectionCovariantDerivative_weighted_inner_integral
    (d : Data) (q : X → ℝ) (U V : X → SphereSobolev 1)
    (S : Set X) (hS : IsCompact S) (hq : ∀ x ∈ S,ContDiffAt ℝ ∞ q x)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) (a : X) :
    (∫ x,oneSectionCovariantInnerDensity d q U V a x)=0 :=
  (oneSectionCovariantDerivative_weighted_inner_data d q U V S hS hq hU hV h0U h0V a).2

end ShrinkingSpheres
