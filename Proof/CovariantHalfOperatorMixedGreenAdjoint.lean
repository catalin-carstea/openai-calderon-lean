import Proof.SupportedHalfCovariantSections
import Proof.CovariantHalfOperatorMixedGreen
import Proof.PhysicalAdjointDerivativeDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OperatorForms

/-- The mixed covariant Green identity with its differentiated coefficient
grouped into the actual weak adjoint density. Its integrability is part of
the assertion, so rearranging the three summands is justified. -/
theorem covariant_half_operator_mixed_green_adjoint {Y : Set X} (hY : IsOpen Y) (d : Data)
    {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U V : X → SphereSobolev (3/2:ℝ)) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC : ContDiffOn ℝ ∞ C Y) (hChS : ContDiffOn ℝ ∞ Ch Y)
    (hCh : ∀ y ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) (b : I) :
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    let D := fun W y => halfSectionCovariantDerivativeL d W y (axis b)
    let N := fun y => metricDensity d.γ y •
      (C y (D V y)+halfOperatorCovariantDerivativeL d C Ch y (axis b) (V y))+
      fderiv ℝ (metricDensity d.γ) y (axis b) • C y (J (V y))
    IntegrableOn (fun y => sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (N y)) Y ∧
      (∫ y in Y,metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ) (D U y) (C y (J (V y))))=
        -(∫ y in Y,sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (N y)) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let μ := metricDensity d.γ
  let DU := fun y => halfSectionCovariantDerivativeL d U y (axis b)
  let DV := fun y => halfSectionCovariantDerivativeL d V y (axis b)
  let C0 := fun y => (C y).comp J
  let Cd := fun y => halfOperatorCovariantDerivativeL d C Ch y (axis b)
  let A := fun y => fderiv ℝ μ y (axis b)*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C0 y (V y))
  let B := fun y => μ y*sphereSobolevDualPairing (1/2:ℝ) (DU y) (C0 y (V y))
  let F := fun y => μ y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (DV y))
  let H := fun y => μ y*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (Cd y (V y))
  have hμ (x) (hx : x ∈ S) : ContDiffAt ℝ ∞ μ x :=
    (hg.contDiffOn_density hK).contDiffAt (hY.mem_nhds (hSY hx))
  have hC0 : ContDiffOn ℝ ∞ C0 Y := hC.clm_comp contDiffOn_const
  have hCd : ContDiffOn ℝ ∞ Cd Y :=
    contDiffOn_halfOperatorCovariantDerivativeL hY d hg hK he C Ch hC hChS b
  have hJU : ContDiff ℝ ∞ (fun x => J (U x)) := J.contDiff.comp hU
  have hDU := contDiff_supported_halfSectionCovariantDerivative hY d hg hK he U hU S hS.isClosed hSY h0U (axis b)
  have hDV := contDiff_supported_halfSectionCovariantDerivative hY d hg hK he V hV S hS.isClosed hSY h0V (axis b)
  have hA : Integrable A := integrable_local_weighted_operator_pair (innerSL ℝ)
    (fun x => fderiv ℝ μ x (axis b)) (fun x => J (U x)) V C0 S hS
    (fun x hx => contDiffAt_directional μ x (axis b) (hμ x hx)) hJU hV h0V
    (fun x hx => hC0.contDiffAt (hY.mem_nhds (hSY hx)))
  have hB : Integrable B := integrable_local_weighted_operator_pair (innerSL ℝ) μ
    DU V C0 S hS hμ hDU.1 hV h0V
    (fun x hx => hC0.contDiffAt (hY.mem_nhds (hSY hx)))
  have hF : Integrable F := integrable_local_weighted_operator_pair (innerSL ℝ) μ
    (fun x => J (U x)) DV C S hS hμ hJU hDV.1 hDV.2
    (fun x hx => hC.contDiffAt (hY.mem_nhds (hSY hx)))
  have hH : Integrable H := integrable_local_weighted_operator_pair (innerSL ℝ) μ
    (fun x => J (U x)) V Cd S hS hμ hJU hV h0V
    (fun x hx => hCd.contDiffAt (hY.mem_nhds (hSY hx)))
  have hGreen := covariant_half_operator_mixed_green hY d hg hK he U V hU hV S hS hSY h0U h0V C Ch hC hCh (axis b)
  have hGreen' : (∫ y in Y,F y)=-(∫ y in Y,A y+B y+H y) := by
    simpa only [F,A,B,H,J,C0,Cd,μ,DU,DV,ContinuousLinearMap.comp_apply,
      halfSectionCovariantDerivativeL_apply,
      OAI.AnisotropicCalderon.PrincipalCommutator.directionalFDeriv] using hGreen
  have hPair : (fun y => sphereSobolevDualPairing (1/2:ℝ) (J (U y))
      (μ y • (C y (DV y)+Cd y (V y))+fderiv ℝ μ y (axis b) • C y (J (V y))))=
      fun y => F y+H y+A y := by
    funext y
    simp only [F,H,A,C0,ContinuousLinearMap.comp_apply,sphereSobolevDualPairing,
      inner_add_right,inner_smul_right,mul_add]
  change IntegrableOn _ Y ∧ (∫ y in Y,B y)=-_
  rw [hPair]
  refine ⟨((hF.add hH).add hA).integrableOn,?_⟩
  rw [integral_add (f:=fun y => A y+B y) (g:=H) (hA.add hB).integrableOn hH.integrableOn,
    integral_add (f:=A) (g:=B) hA.integrableOn hB.integrableOn] at hGreen'
  rw [integral_add (f:=fun y => F y+H y) (g:=A) (hF.add hH).integrableOn hA.integrableOn,
    integral_add (f:=F) (g:=H) hF.integrableOn hH.integrableOn]
  linarith only [hGreen']

end ShrinkingSpheres
