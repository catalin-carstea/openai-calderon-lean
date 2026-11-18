import Proof.LocalWeightedOperatorGreen
import Proof.LocalSupportedOperatorPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped ContDiff Topology
open OAI.AnisotropicCalderon OAI.AnisotropicCalderon.PrincipalCommutator
namespace ShrinkingSpheres.OperatorForms
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Bilinear version of the supplied local Green argument. Distinct
supported sections may be used in the mixed operator products. -/
theorem weighted_first_operator_green_mixed_local
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu : R3 → ℝ)
    (u v : R3 → E) (C : R3 → E →L[ℝ] F) (K : Set R3) (hK : IsCompact K)
    (hm : ∀ x ∈ K,ContDiffAt ℝ ∞ mu x) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (h0u : ∀ x ∉ K,u x=0) (h0v : ∀ x ∉ K,v x=0)
    (hC : ∀ x ∈ K,ContDiffAt ℝ ∞ C x) (a : R3) :
    (∫ x,mu x*P (I (u x)) (C x (directionalFDeriv a v x)))=
      -(∫ x,directionalFDeriv a mu x*P (I (u x)) (C x (v x))+
        mu x*P (I (directionalFDeriv a u x)) (C x (v x))+
        mu x*P (I (u x)) (directionalFDeriv a C x (v x))) := by
  let z := fun x => C x (v x)
  let w := fun x => I (u x)
  let f := fun x => mu x • w x
  have hw : ContDiff ℝ ∞ w := contDiff_const.clm_apply hu
  have hz : ContDiff ℝ ∞ z := contDiff_supported_operator_apply v C K hK.isClosed hv h0v hC
  have hzc : HasCompactSupport z := compact_supported_operator_apply v C K hK h0v
  have hw0 (x) (hx : x ∉ K) : w x=0 := by simp only [w,h0u x hx,map_zero]
  have hf : ContDiff ℝ ∞ f := contDiff_supported_smul mu w K hK.isClosed hw hw0 hm
  have hfi := compact_bilinear_integrable P _ z (contDiff_directionalFDeriv a f hf).continuous hz.continuous hzc
  have hzi := compact_bilinear_integrable P f _ hf.continuous
    (contDiff_directionalFDeriv a z hz).continuous (hzc.fderiv_apply (𝕜:=ℝ) a)
  have hbase := compact_bilinear_integrable P f z hf.continuous hz.continuous hzc
  have hg := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B:=P) (v:=a) hfi hzi hbase
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hz.differentiable (by simp) x)
  have hzD (x) : directionalFDeriv a z x=directionalFDeriv a C x (v x)+C x (directionalFDeriv a v x) :=
    directional_operator_apply_supported v C K hK.isClosed hv h0v hC a x
  have hfD (x) : directionalFDeriv a f x=
      directionalFDeriv a mu x • I (u x)+mu x • I (directionalFDeriv a u x) := by
    have h := directional_smul_supported mu w K hK.isClosed hw hw0 hm a x
    rw [directional_linear_input I u hu a x] at h
    exact h
  let A := fun x => mu x*P (I (u x)) (C x (directionalFDeriv a v x))
  let B := fun x => mu x*P (I (u x)) (directionalFDeriv a C x (v x))
  let D := fun x => directionalFDeriv a mu x*P (I (u x)) (C x (v x))+
    mu x*P (I (directionalFDeriv a u x)) (C x (v x))
  have hAB : (fun x => P (f x) (directionalFDeriv a z x))=fun x => A x+B x := by
    funext x
    rw [hzD x]
    simp only [f,w,A,B,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,map_add]
    ring
  have hD : (fun x => P (directionalFDeriv a f x) (z x))=D := by
    funext x
    rw [hfD x]
    simp only [D,z,map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hBi : Integrable B :=
    integrable_local_weighted_operator_pair P mu w v (directionalFDeriv a C) K hK hm hw hv h0v
      (fun x hx => contDiffAt_directional C x a (hC x hx))
  have hAi : Integrable A := by
    rw [hAB] at hzi
    exact (hzi.sub hBi).congr (by filter_upwards [] with x;exact add_sub_cancel_right _ _)
  have hDi : Integrable D := by rw [←hD];exact hfi
  change (∫ x,A x)=-(∫ x,D x+B x)
  change (∫ x,P (f x) (directionalFDeriv a z x))=-(∫ x,P (directionalFDeriv a f x) (z x)) at hg
  rw [hAB,hD,integral_add hAi hBi] at hg
  rw [integral_add hDi hBi]
  linarith
end ShrinkingSpheres.OperatorForms
