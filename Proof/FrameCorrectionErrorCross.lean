import Proof.ActualRadialTaylorEndpoints
import Proof.ActualFrameCorrectionGraded
import Proof.BoundedCompositionCross
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Both F/E compositions, with the canonical SAME F at its genuine grades. -/
def frameCorrectionErrorCrossL (d : Data)
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,∑ j : I,Q x i j •
    (((firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d x i).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))).comp (H j x)+
      (L i x).comp ((firstFrameAdjointCorrectionAtL (1/2:ℝ) d x j).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))))

lemma norm_frameCorrectionErrorCrossL_le (d : Data)
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X) {B q CL CH : ℝ}
    (hB : 0 ≤ B) (hq : 0 ≤ q) (hCL : 0 ≤ CL) (hCH : 0 ≤ CH)
    (hQ : ∀ i j,|Q x i j| ≤ B) (hL : ∀ i,‖L i x‖ ≤ q) (hH : ∀ j,‖H j x‖ ≤ q)
    (hFL : ∀ i,‖firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d x i‖ ≤ CL)
    (hFH : ∀ j,‖firstFrameAdjointCorrectionAtL (1/2:ℝ) d x j‖ ≤ CH) :
    ‖frameCorrectionErrorCrossL d L H Q x‖ ≤ 9*B*(CL+CH)*q := by
  let F (i : I) := (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d x i).comp
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
  let G (j : I) := (firstFrameAdjointCorrectionAtL (1/2:ℝ) d x j).comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  have hF (i : I) : ‖F i‖ ≤ CL :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul (hFL i)
      (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _) hCL).trans_eq (mul_one _))
  have hG (j : I) : ‖G j‖ ≤ CH :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul (hFH j)
      (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _) hCH).trans_eq (mul_one _))
  have hEach (i j : I) : ‖Q x i j • ((F i).comp (H j x)+(L i x).comp (G j))‖ ≤ B*(CL+CH)*q := by
    have hh := norm_bounded_composition_cross_le _ _ _ _ hCL hq (hF i) (hG j) (hL i) (hH j)
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hQ i j) hh (norm_nonneg _) hB).trans_eq (by ring)
  calc
    _ ≤ ∑ i : I,∑ j : I,‖Q x i j • ((F i).comp (H j x)+(L i x).comp (G j))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : I,∑ _j : I,B*(CL+CH)*q :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEach i j))
    _ = _ := by simp only [Fin.sum_univ_three];ring

lemma Admissible.contDiffOn_frameCorrectionErrorCrossL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ)
    (hL : ∀ i,ContDiffOn ℝ ∞ (L i) Y) (hH : ∀ j,ContDiffOn ℝ ∞ (H j) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => Q x i j) Y) :
    ContDiffOn ℝ ∞ (frameCorrectionErrorCrossL d L H Q) Y := by
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hQ i j).smul
    ((((hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK (-(1/2:ℝ)) i).clm_comp
      contDiffOn_const).clm_comp (hH j)).add
        ((hL i).clm_comp ((hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK (1/2:ℝ) j).clm_comp
          contDiffOn_const)))))

/-- The controlled F/E coefficient is the actual physical two-sided cross
    on arbitrary genuine H1 output lifts of the SAME first errors. -/
lemma frameCorrectionErrorCrossL_actual_lifts (d : Data)
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X)
    (E : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (u : SphereSobolev 2)
    (v : I → SphereSobolev 1)
    (hE : ∀ i,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (E i)=
      (L i x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hV : ∀ j,sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (v j)=
      H j x (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (∑ i : I,∑ j : I,Q x i j •
        (firstFrameAdjointCorrectionL d x i (sphereSobolevInclusionL 1 0 (by norm_num) (v j))+
          E i (firstFrameAdjointCorrectionSobolevL d x j
            (sphereSobolevInclusionL 2 1 (by norm_num) u))))=
      frameCorrectionErrorCrossL d L H Q x
        (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  simp only [frameCorrectionErrorCrossL,map_sum,map_smul,map_add,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => Q x i j • z)
  have hFi := firstFrameAdjointCorrectionAtL_inclusion 0 (-(1/2:ℝ)) (by norm_num)
    d x i (sphereSobolevInclusionL 1 0 (by norm_num) (v j))
  rw [firstFrameAdjointCorrectionAtL_zero] at hFi
  have hFj := firstFrameAdjointCorrectionAtL_inclusion 1 (1/2:ℝ) (by norm_num)
    d x j (sphereSobolevInclusionL 2 1 (by norm_num) u)
  rw [firstFrameAdjointCorrectionAtL_one] at hFj
  have hEi := DFunLike.congr_fun (hE i)
    (firstFrameAdjointCorrectionSobolevL d x j (sphereSobolevInclusionL 2 1 (by norm_num) u))
  simp only [ContinuousLinearMap.comp_apply] at hEi
  have hIv : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevInclusionL 1 0 (by norm_num) (v j))=
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
          (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (v j)) := by
    rw [sphereSobolevInclusionL_trans_apply,sphereSobolevInclusionL_trans_apply]
  have hIu : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
      (sphereSobolevInclusionL 2 1 (by norm_num) u)=
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
          (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
    rw [sphereSobolevInclusionL_trans_apply,sphereSobolevInclusionL_trans_apply]
  rw [hFi,hIv,hV j,hEi,hFj,hIu]

def radiusFrameCorrectionErrorCrossL (d : Data)
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  d.radius x • frameCorrectionErrorCrossL d L H Q x

lemma norm_radiusFrameCorrectionErrorCrossL_small (d : Data)
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X) {B CE CL CH ε : ℝ}
    (hB : 0 ≤ B) (hCE : 0 ≤ CE) (hCL : 0 ≤ CL) (hCH : 0 ≤ CH)
    (hr : 0 ≤ d.radius x) (hr1 : d.radius x ≤ 1) (hrε : d.radius x ≤ ε)
    (hQ : ∀ i j,|Q x i j| ≤ B)
    (hL : ∀ i,‖L i x‖ ≤ CE*d.radius x) (hH : ∀ j,‖H j x‖ ≤ CE*d.radius x)
    (hFL : ∀ i,‖firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d x i‖ ≤ CL)
    (hFH : ∀ j,‖firstFrameAdjointCorrectionAtL (1/2:ℝ) d x j‖ ≤ CH) :
    ‖radiusFrameCorrectionErrorCrossL d L H Q x‖ ≤ 9*B*(CL+CH)*CE*ε := by
  have hr2 : (d.radius x)^2 ≤ ε :=
    (by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1)] : (d.radius x)^2 ≤ d.radius x).trans hrε
  rw [radiusFrameCorrectionErrorCrossL,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  calc
    _ ≤ d.radius x*(9*B*(CL+CH)*(CE*d.radius x)) :=
      mul_le_mul_of_nonneg_left (norm_frameCorrectionErrorCrossL_le d L H Q x
        hB (mul_nonneg hCE hr) hCL hCH hQ hL hH hFL hFH) hr
    _ = (9*B*(CL+CH)*CE)*(d.radius x)^2 := by ring
    _ ≤ (9*B*(CL+CH)*CE)*ε := mul_le_mul_of_nonneg_left hr2 (by positivity)
end ShrinkingSpheres
