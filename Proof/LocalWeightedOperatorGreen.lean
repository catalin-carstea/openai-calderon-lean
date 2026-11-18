/- Generic weighted operator Green identities adopted from the selected ZIP; quantitative special-radius producers excluded. -/
import Proof.SupportedOperatorCalculus
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
open OAI.AnisotropicCalderon OAI.AnisotropicCalderon.PrincipalCommutator
namespace ShrinkingSpheres.OperatorForms
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem weighted_second_operator_green_local
    (P : E →L[ℝ] F →L[ℝ] ℝ) (mu : R3 → ℝ) (u : R3 → E)
    (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ∀ x ∈ K,ContDiffAt ℝ ∞ mu x) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (X Y : R3) :
    (∫ x, mu x * P (u x) (C x (directionalFDeriv X (directionalFDeriv Y u) x))) =
      -(∫ x, (directionalFDeriv X mu x)*P (u x) (C x (directionalFDeriv Y u x))+
        mu x*P (directionalFDeriv X u x) (C x (directionalFDeriv Y u x))+
        mu x*P (u x) ((directionalFDeriv X C x) (directionalFDeriv Y u x))) := by
  let v : R3 → E := directionalFDeriv Y u
  let z : R3 → F := fun x => C x (v x)
  let f : R3 → E := fun x => mu x • u x
  have hv : ContDiff ℝ ∞ v := contDiff_directionalFDeriv Y u hu
  have hv0 : ∀ x ∉ K, v x = 0 := fun x hx => directional_eq_zero_off u K hK.isClosed h0 Y x hx
  have hz : ContDiff ℝ ∞ z := contDiff_supported_operator_apply v C K hK.isClosed hv hv0 hC
  have hzc : HasCompactSupport z := compact_supported_operator_apply v C K hK hv0
  have hf : ContDiff ℝ ∞ f := contDiff_supported_smul mu u K hK.isClosed hu h0 hm
  have hfi : Integrable (fun x => P (directionalFDeriv X f x) (z x)) :=
    compact_bilinear_integrable P _ _ (contDiff_directionalFDeriv X f hf).continuous hz.continuous hzc
  have hzi : Integrable (fun x => P (f x) (directionalFDeriv X z x)) :=
    compact_bilinear_integrable P _ _ hf.continuous (contDiff_directionalFDeriv X z hz).continuous
      (hzc.fderiv_apply (𝕜 := ℝ) X)
  have hbase : Integrable (fun x => P (f x) (z x)) :=
    compact_bilinear_integrable P _ _ hf.continuous hz.continuous hzc
  have hg := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := P) (v := X) hfi hzi hbase
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hz.differentiable (by simp) x)
  have hzD (x : R3) : directionalFDeriv X z x =
      directionalFDeriv X C x (v x)+C x (directionalFDeriv X v x) :=
    directional_operator_apply_supported v C K hK.isClosed hv hv0 hC X x
  have hfD (x : R3) : directionalFDeriv X f x =
      directionalFDeriv X mu x • u x+mu x • directionalFDeriv X u x :=
    directional_smul_supported mu u K hK.isClosed hu h0 hm X x
  let A : R3 → ℝ := fun x => mu x*P (u x) (C x (directionalFDeriv X v x))
  let B : R3 → ℝ := fun x => mu x*P (u x) ((directionalFDeriv X C x) (v x))
  let D : R3 → ℝ := fun x => directionalFDeriv X mu x*P (u x) (C x (v x))+
      mu x*P (directionalFDeriv X u x) (C x (v x))
  have hAB : (fun x => P (f x) (directionalFDeriv X z x)) = fun x => A x+B x := by
    funext x
    rw [hzD x]
    simp only [f,A,B,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,map_add]
    ring
  have hD : (fun x => P (directionalFDeriv X f x) (z x)) = D := by
    funext x
    rw [hfD x]
    simp only [D,z,map_add,map_smul,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hBC : ContDiff ℝ ∞ (fun x => (directionalFDeriv X C x) (v x)) :=
    contDiff_supported_operator_apply v _ K hK.isClosed hv hv0
      (fun x hx => contDiffAt_directional C x X (hC x hx))
  have hBi : Integrable B := by
    have hh := compact_bilinear_integrable P f _ hf.continuous hBC.continuous
      (compact_supported_operator_apply v _ K hK hv0)
    convert hh using 1
    funext x
    simp only [B,f,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hAi : Integrable A := by
    have h := hzi
    rw [hAB] at h
    exact (h.sub hBi).congr (by filter_upwards [] with x; exact add_sub_cancel_right _ _)
  have hDi : Integrable D := by rw [←hD]; exact hfi
  change (∫ x, A x) = -(∫ x, D x+B x)
  change (∫ x, P (f x) (directionalFDeriv X z x)) =
    -(∫ x, P (directionalFDeriv X f x) (z x)) at hg
  rw [hAB,hD,integral_add hAi hBi] at hg
  rw [integral_add hDi hBi]
  linarith

theorem weighted_first_operator_green_local
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (mu : R3 → ℝ)
    (u : R3 → E) (C : R3 → (E →L[ℝ] F)) (K : Set R3) (hK : IsCompact K)
    (hm : ∀ x ∈ K,ContDiffAt ℝ ∞ mu x) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x) (X : R3) :
    (∫ x, mu x*P (I (u x)) (C x (directionalFDeriv X u x))) =
      -(∫ x, directionalFDeriv X mu x*P (I (u x)) (C x (u x))+
        mu x*P (I (directionalFDeriv X u x)) (C x (u x))+
        mu x*P (I (u x)) ((directionalFDeriv X C x) (u x))) := by
  let z : R3 → F := fun x => C x (u x)
  let v : R3 → G := fun x => I (u x)
  let f : R3 → G := fun x => mu x • v x
  have hv : ContDiff ℝ ∞ v := contDiff_const.clm_apply hu
  have hz : ContDiff ℝ ∞ z := contDiff_supported_operator_apply u C K hK.isClosed hu h0 hC
  have hzc : HasCompactSupport z := compact_supported_operator_apply u C K hK h0
  have hf : ContDiff ℝ ∞ f := contDiff_supported_smul mu v K hK.isClosed hv
    (fun x hx => by dsimp only [v];rw [h0 x hx,map_zero]) hm
  have hfi := compact_bilinear_integrable P _ z (contDiff_directionalFDeriv X f hf).continuous hz.continuous hzc
  have hzi := compact_bilinear_integrable P f _ hf.continuous
    (contDiff_directionalFDeriv X z hz).continuous (hzc.fderiv_apply (𝕜 := ℝ) X)
  have hbase := compact_bilinear_integrable P f z hf.continuous hz.continuous hzc
  have hg := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := P) (v := X) hfi hzi hbase
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hz.differentiable (by simp) x)
  have hzD (x : R3) : directionalFDeriv X z x =
      directionalFDeriv X C x (u x)+C x (directionalFDeriv X u x) :=
    directional_operator_apply_supported u C K hK.isClosed hu h0 hC X x
  have hfD (x : R3) : directionalFDeriv X f x =
      directionalFDeriv X mu x • I (u x)+mu x • I (directionalFDeriv X u x) := by
    have h := directional_smul_supported mu v K hK.isClosed hv
      (fun x hx => by dsimp only [v];rw [h0 x hx,map_zero]) hm X x
    have hI : directionalFDeriv X v x = I (directionalFDeriv X u x) := directional_linear_input I u hu X x
    rw [hI] at h
    exact h
  let A : R3 → ℝ := fun x => mu x*P (I (u x)) (C x (directionalFDeriv X u x))
  let B : R3 → ℝ := fun x => mu x*P (I (u x)) ((directionalFDeriv X C x) (u x))
  let D : R3 → ℝ := fun x => directionalFDeriv X mu x*P (I (u x)) (C x (u x))+
      mu x*P (I (directionalFDeriv X u x)) (C x (u x))
  have hAB : (fun x => P (f x) (directionalFDeriv X z x)) = fun x => A x+B x := by
    funext x
    rw [hzD x]
    simp only [f,v,A,B,map_smul,smul_apply,smul_eq_mul,map_add]
    ring
  have hD : (fun x => P (directionalFDeriv X f x) (z x)) = D := by
    funext x
    rw [hfD x]
    simp only [D,z,map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  have hBC := contDiff_supported_operator_apply u (directionalFDeriv X C) K hK.isClosed hu h0
    (fun x hx => contDiffAt_directional C x X (hC x hx))
  have hBi : Integrable B := by
    have h := compact_bilinear_integrable P f _ hf.continuous hBC.continuous
      (compact_supported_operator_apply u _ K hK h0)
    convert h using 1
    funext x
    simp only [f,v,B,map_smul,smul_apply,smul_eq_mul]
  have hAi : Integrable A := by
    have h := hzi
    rw [hAB] at h
    exact (h.sub hBi).congr (by filter_upwards [] with x; exact add_sub_cancel_right _ _)
  have hDi : Integrable D := by rw [←hD]; exact hfi
  change (∫ x, A x) = -(∫ x, D x+B x)
  change (∫ x, P (f x) (directionalFDeriv X z x)) =
    -(∫ x, P (directionalFDeriv X f x) (z x)) at hg
  rw [hAB,hD,integral_add hAi hBi] at hg
  rw [integral_add hDi hBi]
  linarith

 
end ShrinkingSpheres.OperatorForms
