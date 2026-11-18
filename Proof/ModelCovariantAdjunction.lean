import Proof.ModelCovariantGreenPoint
import Proof.LocalSupportedOperatorPairing

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
open OAI.AnisotropicCalderon.DirichletFamily OperatorForms

/-- The manuscript model-adjoint identity on the genuine common core:
T-dagger = T-flat minus the SAME sum f_i A_i. Individual integrability
and actual covariant Green are proved, including all frame divergences. -/
theorem model_covariant_full_adjunction_data {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (U V : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) :
    let I20 := (sphereSobolevInclusionL 1 0 (by norm_num)).comp (sphereSobolevInclusionL 2 1 (by norm_num))
    let L := fun x => metricDensity d.γ x*⟪modelRaisingSection d U x,I20 (V x)⟫_ℝ
    let R := fun x => metricDensity d.γ x*⟪I20 (U x),modelLoweringSection d V x-modelAdjointDefectSection d V x⟫_ℝ
    IntegrableOn L Y ∧ IntegrableOn R Y ∧ (∫ x in Y,L x)=(∫ x in Y,R x) := by
  let I21 := sphereSobolevInclusionL 2 1 (by norm_num)
  let I20 := (sphereSobolevInclusionL 1 0 (by norm_num)).comp I21
  let U1 := fun x => I21 (U x)
  let W := fun (i : I) x => flatLoweringSobolevL 2 i (V x)
  let Rop := fun x => modelLoweringSection d V x-modelAdjointDefectSection d V x
  let L := fun x => metricDensity d.γ x*⟪modelRaisingSection d U x,I20 (V x)⟫_ℝ
  let R := fun x => metricDensity d.γ x*⟪I20 (U x),Rop x⟫_ℝ
  let G0 := fun (i : I) => oneSectionCovariantVectorInnerDensity d (metricDensity d.γ) U1 (W i) (fun x => d.frame x i)
  let G := fun x => ∑ i : I,G0 i x
  have hmu (x : X) (hx : x ∈ S) : ContDiffAt ℝ ∞ (metricDensity d.γ) x :=
    (hg.contDiffOn_density hK).contDiffAt (hY.mem_nhds (hSY hx))
  have hFrameS (i : I) (x : X) (hx : x ∈ S) : ContDiffAt ℝ ∞ (fun z => d.frame z i) x :=
    (he i).contDiffAt (hY.mem_nhds (hSY hx))
  have hU1 : ContDiff ℝ ∞ U1 := I21.contDiff.comp hU
  have hW (i : I) : ContDiff ℝ ∞ (W i) := (flatLoweringSobolevL 2 i).contDiff.comp hV
  have h0U1 (x : X) (hx : x ∉ S) : U1 x=0 := by dsimp only [U1];rw [h0U x hx,map_zero]
  have h0W (i : I) (x : X) (hx : x ∉ S) : W i x=0 := by dsimp only [W];rw [h0V x hx,map_zero]
  have hData (i : I) := oneSectionCovariantDerivative_vector_inner_data d (metricDensity d.γ) U1 (W i)
    (fun x => d.frame x i) S hS hmu (hFrameS i) hU1 (hW i) h0U1 (h0W i)
  have hGI : Integrable G := integrable_finsetSum Finset.univ (fun i _ => (hData i).1)
  have hGOff (x : X) (hx : x ∉ Y) : G x=0 := by
    have hxS : x ∉ S := fun hs => hx (hSY hs)
    have hD (i : I) := oneSectionCovariantDerivative_zero_off d U1 S hS.isClosed h0U1 (d.frame x i) x hxS
    simp only [G,G0,oneSectionCovariantVectorInnerDensity,h0U1 x hxS,hD,map_zero,
      inner_zero_left,zero_mul,mul_zero,zero_add,add_zero,Finset.sum_const_zero]
  have hGY : (∫ x in Y,G x)=0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hGOff]
    change (∫ x,∑ i : I,G0 i x)=0
    rw [integral_finsetSum Finset.univ (fun i _ => (hData i).1)]
    simp only [G0,(hData _).2,Finset.sum_const_zero]
  have hSU := contDiff_supported_modelCovariantSections hY d hg hK he hlog U hU S hS.isClosed hSY h0U
  have hSV := contDiff_supported_modelCovariantSections hY d hg hK he hlog V hV S hS.isClosed hSY h0V
  have hRop : ContDiff ℝ ∞ Rop := hSV.2.1.sub hSV.2.2
  have h0Rop (x : X) (hx : x ∉ S) : Rop x=0 := by
    have hh := modelCovariantSections_zero_off d V S hS.isClosed h0V x hx
    simp only [Rop,hh.2.1,hh.2.2,sub_self]
  have h0IV (x : X) (hx : x ∉ S) : I20 (V x)=0 := by rw [h0V x hx,map_zero]
  have hLI : Integrable L := integrable_local_weighted_operator_pair (innerSL ℝ) (metricDensity d.γ)
    (modelRaisingSection d U) (fun x => I20 (V x)) (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0))
    S hS hmu hSU.1 (I20.contDiff.comp hV) h0IV (fun _ _ => contDiffAt_const)
  have hRI : Integrable R := integrable_local_weighted_operator_pair (innerSL ℝ) (metricDensity d.γ)
    (fun x => I20 (U x)) Rop (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0))
    S hS hmu (I20.contDiff.comp hU) hRop h0Rop (fun _ _ => contDiffAt_const)
  have hEq : (fun x => L x-R x) =ᵐ[volume.restrict Y] G := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    calc
      _ = metricDensity d.γ x*(⟪modelRaisingSection d U x,I20 (V x)⟫_ℝ-
          ⟪I20 (U x),modelLoweringSection d V x-modelAdjointDefectSection d V x⟫_ℝ) := by
        dsimp only [L,R,Rop];ring
      _ = _ := model_covariant_green_point hY d hg hK he hFrame Q hQ U V hx
        (hU.differentiable (by simp) x) (hV.differentiable (by simp) x)
  have hLR : (∫ x in Y,L x)-(∫ x in Y,R x)=0 := by
    calc
      _ = ∫ x in Y,L x-R x := (integral_sub hLI.integrableOn hRI.integrableOn).symm
      _ = ∫ x in Y,G x := integral_congr_ae hEq
      _ = 0 := hGY
  exact ⟨hLI.integrableOn,hRI.integrableOn,sub_eq_zero.mp hLR⟩

end ShrinkingSpheres
