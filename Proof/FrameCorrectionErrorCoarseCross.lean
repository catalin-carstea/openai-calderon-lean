import Proof.FrameCorrectionErrorCross
import Proof.BalancedCoarsePotential
import Proof.FiniteMatrixNormBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine order-one F/E cross, using each F at the grade required
by its actual composition. -/
def frameCorrectionErrorCoarseCrossL (d : Data)
    (E : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,∑ j : I,Q x i j •
    ((firstFrameAdjointCorrectionAtL 0 d x i).comp (E j x)+
      (E i x).comp (firstFrameAdjointCorrectionAtL 1 d x j))

def radiusFrameCorrectionErrorCoarseCrossL (d : Data)
    (E : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  d.radius x • frameCorrectionErrorCoarseCrossL d E Q x

lemma frameCorrectionErrorCoarseCrossL_balanced (d : Data)
    (E : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X)
    (hL : ∀ i,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (E i x)=
      (L i x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hH : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H j x)=
      (E j x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    balancedCoarsePotentialL (frameCorrectionErrorCoarseCrossL d E Q x)=frameCorrectionErrorCrossL d L H Q x := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [balancedCoarsePotentialL,frameCorrectionErrorCoarseCrossL,frameCorrectionErrorCrossL,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,_root_.add_apply,map_sum,map_smul,map_add]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => Q x i j • z)
  have hEj := DFunLike.congr_fun (hH j) u
  simp only [ContinuousLinearMap.comp_apply] at hEj
  have hEI : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (E j x (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))=
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (H j x u) := by
    rw [←hEj,sphereSobolevInclusionL_trans_apply]
  have hF0 := firstFrameAdjointCorrectionAtL_inclusion 0 (-(1/2:ℝ)) (by norm_num) d x i
    (E j x (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))
  have hFirst := hF0.trans (congrArg (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d x i) hEI)
  have hEi := DFunLike.congr_fun (hL i)
    (firstFrameAdjointCorrectionAtL 1 d x j (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))
  simp only [ContinuousLinearMap.comp_apply] at hEi
  have hF1 := firstFrameAdjointCorrectionAtL_inclusion 1 (1/2:ℝ) (by norm_num) d x j
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
  simp only [sphereSobolevInclusionL_trans_apply] at hF1
  exact congrArg₂ (fun v w : SphereSobolev (-(1/2:ℝ)) => v+w) hFirst
    (hEi.trans (congrArg (L i x) hF1))

lemma norm_radiusFrameCorrectionErrorCoarseCrossL_small (d : Data)
    (E : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : X → I → I → ℝ) (x : X)
    {B CE C0 C1 ε : ℝ} (hB : 0 ≤ B) (hCE : 0 ≤ CE) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hr : 0 ≤ d.radius x) (hr1 : d.radius x ≤ 1) (hrε : d.radius x ≤ ε)
    (hQ : ∀ i j,|Q x i j| ≤ B) (hE : ∀ i,‖E i x‖ ≤ CE*d.radius x)
    (hF0 : ∀ i,‖firstFrameAdjointCorrectionAtL 0 d x i‖ ≤ C0)
    (hF1 : ∀ j,‖firstFrameAdjointCorrectionAtL 1 d x j‖ ≤ C1) :
    ‖radiusFrameCorrectionErrorCoarseCrossL d E Q x‖ ≤ 9*B*(C0+C1)*CE*ε := by
  have hq : 0 ≤ CE*d.radius x := mul_nonneg hCE hr
  have hEach (i j : I) : ‖(firstFrameAdjointCorrectionAtL 0 d x i).comp (E j x)+
      (E i x).comp (firstFrameAdjointCorrectionAtL 1 d x j)‖ ≤ (C0+C1)*(CE*d.radius x) := by
    calc
      _ ≤ ‖(firstFrameAdjointCorrectionAtL 0 d x i).comp (E j x)‖+
        ‖(E i x).comp (firstFrameAdjointCorrectionAtL 1 d x j)‖ := norm_add_le _ _
      _ ≤ ‖firstFrameAdjointCorrectionAtL 0 d x i‖*‖E j x‖+
        ‖E i x‖*‖firstFrameAdjointCorrectionAtL 1 d x j‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ C0*(CE*d.radius x)+(CE*d.radius x)*C1 := add_le_add
        (mul_le_mul (hF0 i) (hE j) (norm_nonneg _) hC0)
        (mul_le_mul (hE i) (hF1 j) (norm_nonneg _) hq)
      _ = _ := by ring
  have hTotal : ‖frameCorrectionErrorCoarseCrossL d E Q x‖ ≤ 9*B*((C0+C1)*(CE*d.radius x)) :=
    norm_weighted_matrix_three_le (Q x) _ B _ hB hQ hEach
  have hr2 : (d.radius x)^2 ≤ ε :=
    (by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1)] : (d.radius x)^2 ≤ d.radius x).trans hrε
  rw [radiusFrameCorrectionErrorCoarseCrossL,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  calc
    _ ≤ d.radius x*(9*B*((C0+C1)*(CE*d.radius x))) := mul_le_mul_of_nonneg_left hTotal hr
    _ = (9*B*(C0+C1)*CE)*(d.radius x)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr2 (by positivity)
end ShrinkingSpheres
