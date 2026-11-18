import Proof.ShiftedDegreeInclusion
import Proof.FrameErrorMatrixRaisingCross
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def frameErrorMatrixDegreeCrossL
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (t : I → X → ℝ) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,∑ j : I,Q x i j •
    ((t i x • sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (H j x)+
      (L i x).comp (t j x • sphereSobolevShiftedDegreeL (3/2:ℝ)))

lemma norm_frameErrorMatrixDegreeCrossL_le
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (t : I → X → ℝ) (x : X) {B q : ℝ} (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hQ : ∀ i j,|Q x i j| ≤ B) (ht : ∀ i,|t i x| ≤ 1)
    (hL : ∀ i,‖L i x‖ ≤ q) (hH : ∀ j,‖H j x‖ ≤ q) :
    ‖frameErrorMatrixDegreeCrossL L H Q t x‖ ≤ 36*B*q := by
  have hD (s : ℝ) (i : I) : ‖t i x • sphereSobolevShiftedDegreeL s‖ ≤ 2 := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (ht i) (norm_sphereSobolevShiftedDegreeL_le_two s)
      (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hEach (i j : I) :
      ‖Q x i j • ((t i x • sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (H j x)+
        (L i x).comp (t j x • sphereSobolevShiftedDegreeL (3/2:ℝ)))‖ ≤ 4*B*q := by
    have hh : ‖(t i x • sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (H j x)+
        (L i x).comp (t j x • sphereSobolevShiftedDegreeL (3/2:ℝ))‖ ≤ (2+2)*q :=
      norm_bounded_composition_cross_le _ _ _ _ (by norm_num) hq
        (hD (1/2:ℝ) i) (hD (3/2:ℝ) j) (hL i) (hH j)
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hQ i j) hh (norm_nonneg _) hB).trans_eq (by ring)
  calc
    _ ≤ ∑ i : I,∑ j : I,
        ‖Q x i j • ((t i x • sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (H j x)+
          (L i x).comp (t j x • sphereSobolevShiftedDegreeL (3/2:ℝ)))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : I,∑ _j : I,4*B*q :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEach i j))
    _ = _ := by simp only [Fin.sum_univ_three];ring

lemma contDiffOn_frameErrorMatrixDegreeCrossL {Y : Set X}
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (t : I → X → ℝ)
    (hL : ∀ i,ContDiffOn ℝ ∞ (L i) Y) (hH : ∀ j,ContDiffOn ℝ ∞ (H j) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => Q x i j) Y) (ht : ∀ i,ContDiffOn ℝ ∞ (t i) Y) :
    ContDiffOn ℝ ∞ (frameErrorMatrixDegreeCrossL L H Q t) Y :=
  ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hQ i j).smul
    ((((ht i).smul contDiffOn_const).clm_comp (hH j)).add
      ((hL i).clm_comp ((ht j).smul contDiffOn_const)))))

/-- Exact degree/error cross on the SAME physical error output lifts. -/
lemma frameErrorMatrixDegreeCrossL_actual_lifts
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (t : I → X → ℝ) (x : X)
    (E : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (u : SphereSobolev 2)
    (v : I → SphereSobolev 1)
    (hE : ∀ i,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (E i)=
      (L i x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hV : ∀ j,sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (v j)=
      H j x (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (∑ i : I,∑ j : I,Q x i j •
        (t i x • sphereSobolevDegreeL (v j)+t j x • E i (sphereSobolevShiftedDegreeL 2 u)))=
      frameErrorMatrixDegreeCrossL L H Q t x
        (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  simp only [frameErrorMatrixDegreeCrossL,map_sum,map_smul,map_add,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => Q x i j • z)
  have hED := DFunLike.congr_fun (hE i) (sphereSobolevShiftedDegreeL 2 u)
  simp only [ContinuousLinearMap.comp_apply] at hED
  rw [sphereSobolevDegreeL_half,hV j,hED,sphereSobolevShiftedDegreeL_threehalf_high]
end ShrinkingSpheres
