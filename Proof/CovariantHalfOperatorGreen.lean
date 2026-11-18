import Proof.LocalWeightedOperatorGreen
import Proof.LocalSupportedOperatorPairing
import Proof.HalfFrameConnectionPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator
open OperatorForms

def halfOperatorCovariantDerivativeL (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  directionalFDeriv a (fun x => (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) y-
    (frameAngularConnectionHalfL d y a).comp (Ch y)+
    (C y).comp (frameAngularConnectionHigherL d y a)

/-- Covariant Green identity with the actual density and angular frame
    connection. The connection cancels exactly; no quantitative frame jet
    hypothesis is added. Coefficients retain genuine compatible endpoints. -/
theorem covariant_half_operator_green {Y : Set X} (hY : IsOpen Y) (d : Data)
    {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev (3/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC : ContDiffOn ℝ ∞ C Y)
    (hCh : ∀ y ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) (a : X) :
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    let V := fun y => J (directionalFDeriv a U y)-frameAngularConnectionHigherL d y a (U y)
    (∫ y in Y,metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (V y)))=
    -(∫ y in Y,directionalFDeriv a (metricDensity d.γ) y*
        sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (J (U y)))+
      metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ) (V y) (C y (J (U y)))+
      metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ) (J (U y))
        (halfOperatorCovariantDerivativeL d C Ch y a (U y))) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let mu := metricDensity d.γ
  let C0 := fun x => (C x).comp J
  let Cd := directionalFDeriv a C0
  let V0 := fun y => J (directionalFDeriv a U y)
  let W := fun y => frameAngularConnectionHigherL d y a (U y)
  let V := fun y => V0 y-W y
  let B := fun y => halfOperatorCovariantDerivativeL d C Ch y a
  let f0 := fun y => mu y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C0 y (directionalFDeriv a U y))
  let f1 := fun y => directionalFDeriv a mu y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C0 y (U y))+
    mu y*sphereSobolevDualPairing (1/2:ℝ) (V0 y) (C0 y (U y))+
    mu y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (Cd y (U y))
  let k := fun y => mu y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (W y))
  let new0 := fun y => mu y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (V y))
  let new1 := fun y => directionalFDeriv a mu y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C0 y (U y))+
    mu y*sphereSobolevDualPairing (1/2:ℝ) (V y) (C0 y (U y))+
    mu y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (B y (U y))
  have hmu (x) (hx : x ∈ S) : ContDiffAt ℝ ∞ mu x :=
    (hg.contDiffOn_density hK).contDiffAt (hY.mem_nhds (hSY hx))
  have hCC (x) (hx : x ∈ S) : ContDiffAt ℝ ∞ C x := hC.contDiffAt (hY.mem_nhds (hSY hx))
  have hC0S : ContDiffOn ℝ ∞ C0 Y := hC.clm_comp contDiffOn_const
  have hC0 (x) (hx : x ∈ S) : ContDiffAt ℝ ∞ C0 x := hC0S.contDiffAt (hY.mem_nhds (hSY hx))
  have hCd (x) (hx : x ∈ S) : ContDiffAt ℝ ∞ Cd x := contDiffAt_directional C0 x a (hC0 x hx)
  have hJUS : ContDiff ℝ ∞ (fun x => J (U x)) := J.contDiff.comp hU
  have hDU := contDiff_directionalFDeriv a U hU
  have hDU0 (x) (hx : x ∉ S) := directional_eq_zero_off U S hS.isClosed h0 a x hx
  have hV0S : ContDiff ℝ ∞ V0 := J.contDiff.comp hDU
  have hRS := contDiffOn_frameAngularConnectionHigherL hY d hg hK he a
  have hWS : ContDiff ℝ ∞ W := contDiff_supported_operator_apply U
    (fun y => frameAngularConnectionHigherL d y a) S hS.isClosed hU h0
      (fun x hx => hRS.contDiffAt (hY.mem_nhds (hSY hx)))
  have hW0 (x) (hx : x ∉ S) : W x=0 := by simp only [W,h0 x hx,map_zero]
  have hf0 : Integrable f0 := integrable_local_weighted_operator_pair (innerSL ℝ) mu
    (fun x => J (U x)) (directionalFDeriv a U) C0 S hS hmu hJUS hDU hDU0 hC0
  have hf1 : Integrable f1 :=
    ((integrable_local_weighted_operator_pair (innerSL ℝ) (directionalFDeriv a mu)
      (fun x => J (U x)) U C0 S hS (fun x hx => contDiffAt_directional mu x a (hmu x hx))
        hJUS hU h0 hC0).add
    (integrable_local_weighted_operator_pair (innerSL ℝ) mu V0 U C0 S hS hmu hV0S hU h0 hC0)).add
    (integrable_local_weighted_operator_pair (innerSL ℝ) mu (fun x => J (U x)) U Cd S hS hmu hJUS hU h0 hCd)
  have hk : Integrable k := integrable_local_weighted_operator_pair (innerSL ℝ) mu
    (fun x => J (U x)) W C S hS hmu hJUS hWS hW0 hCC
  have hRaw : (∫ x,f0 x)=-(∫ x,f1 x) :=
    weighted_first_operator_green_local (innerSL ℝ) J mu U C0 S hS hmu hU h0 hC0 a
  have hOff (x) (hx : x ∉ Y) : U x=0 ∧ directionalFDeriv a U x=0 :=
    ⟨h0 x (fun hs => hx (hSY hs)),hDU0 x (fun hs => hx (hSY hs))⟩
  have hRawY : (∫ x in Y,f0 x)=-(∫ x in Y,f1 x) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp only [f0,(hOff x hx).1,map_zero,sphereSobolevDualPairing,inner_zero_left,mul_zero]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp only [f1,V0,(hOff x hx).1,(hOff x hx).2,map_zero,sphereSobolevDualPairing,
        inner_zero_left,inner_zero_right,mul_zero,add_zero])]
    exact hRaw
  have hNew0 (x : X) : new0 x=f0 x-k x := by
    simp only [new0,f0,k,V,V0,C0,ContinuousLinearMap.comp_apply,map_sub,sphereSobolevDualPairing,
      inner_sub_right,mul_sub]
  have hNew1 (x : X) (hx : x ∈ Y) : new1 x=f1 x+k x := by
    have hPoint := graded_connection_first_integrand T (frameAngularConnectionHalfL d x a) (C x)
      J (Ch x) (frameAngularConnectionHigherL d x a) (Cd x) (B x)
      sphereSobolevHalfNegativeInclusion_adjoint (frameAngularConnectionHalfL_adjoint d x a)
      (hCh x hx) (frameAngularConnectionHigherL_compatible d x a) rfl (U x) (directionalFDeriv a U x)
    dsimp only [new1,f1,k,V,V0,C0] 
    simp only [ContinuousLinearMap.comp_apply,sphereSobolevDualPairing] at hPoint ⊢
    nlinarith only [congrArg (fun z : ℝ => mu x*z) hPoint]
  change (∫ x in Y,new0 x)=-(∫ x in Y,new1 x)
  calc
    _ = ∫ x in Y,f0 x-k x := integral_congr_ae (Eventually.of_forall hNew0)
    _ = (∫ x in Y,f0 x)-(∫ x in Y,k x) := integral_sub hf0.integrableOn hk.integrableOn
    _ = -((∫ x in Y,f1 x)+(∫ x in Y,k x)) := by rw [hRawY];ring
    _ = -(∫ x in Y,f1 x+k x) := congrArg Neg.neg (integral_add hf1.integrableOn hk.integrableOn).symm
    _ = _ := congrArg Neg.neg (integral_congr_ae (by
      filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
      exact (hNew1 x hx).symm))
end ShrinkingSpheres
