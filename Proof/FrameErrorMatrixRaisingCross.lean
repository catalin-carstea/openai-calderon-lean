import Proof.BoundedCompositionCross
import Proof.FrameErrorRaisingHalfCross
import Proof.FlatRaisingCoarseRotation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def frameErrorMatrixRaisingCrossL
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,∑ j : I,Q x i j • ((flatHalfRaisingL i).comp (H j x)+(L i x).comp (flatThreeHalfRaisingL j))

lemma norm_frameErrorMatrixRaisingCrossL_le
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X) {B q : ℝ} (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hQ : ∀ i j,|Q x i j| ≤ B) (hL : ∀ i,‖L i x‖ ≤ q) (hH : ∀ j,‖H j x‖ ≤ q) :
    ‖frameErrorMatrixRaisingCrossL L H Q x‖ ≤
      9*B*(10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ)))*q := by
  let C := 10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ))
  have hEach (i j : I) : ‖Q x i j • ((flatHalfRaisingL i).comp (H j x)+(L i x).comp (flatThreeHalfRaisingL j))‖ ≤ B*C*q := by
    have hCA : 0 ≤ 10*radialDriftSobolevBound (-(1/2:ℝ)) :=
      mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
    have hh : ‖(flatHalfRaisingL i).comp (H j x)+(L i x).comp (flatThreeHalfRaisingL j)‖ ≤ C*q :=
      norm_bounded_composition_cross_le _ _ _ _ hCA hq
      (norm_flatHalfRaisingL_le i) (norm_flatThreeHalfRaisingL_le j) (hL i) (hH j)
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hQ i j) hh (norm_nonneg _) hB).trans_eq (by ring)
  calc
    _ ≤ ∑ i : I,∑ j : I,‖Q x i j • ((flatHalfRaisingL i).comp (H j x)+(L i x).comp (flatThreeHalfRaisingL j))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : I,∑ _j : I,B*C*q := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEach i j))
    _ = _ := by simp only [Fin.sum_univ_three];dsimp only [C];ring

lemma contDiffOn_frameErrorMatrixRaisingCrossL {Y : Set X}
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (hL : ∀ i,ContDiffOn ℝ ∞ (L i) Y)
    (hH : ∀ j,ContDiffOn ℝ ∞ (H j) Y) (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => Q x i j) Y) :
    ContDiffOn ℝ ∞ (frameErrorMatrixRaisingCrossL L H Q) Y :=
  ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hQ i j).smul
    ((contDiffOn_const.clm_comp (hH j)).add ((hL i).clm_comp contDiffOn_const))))

lemma flatOneRaisingL_half (i : I) (v : SphereSobolev 1) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (flatOneRaisingL i v)=
      flatHalfRaisingL i (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v) := by
  have hh := flatRaisingSobolevL_inclusion 1 (1/2:ℝ) (by norm_num) i
  have hI : sphereSobolevInclusionL ((1:ℝ)-1) ((1/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  exact (DFunLike.congr_fun hh v).symm

/-- Full-matrix raising/error cross on actual H1 error output lifts, with all
    genuine endpoint inclusions kept at the declared Sobolev grades. -/
lemma frameErrorMatrixRaisingCrossL_actual_lifts
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Q : X → I → I → ℝ) (x : X) (E : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (u : SphereSobolev 2) (v : I → SphereSobolev 1)
    (hE : ∀ i,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (E i)=
      (L i x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hV : ∀ j,sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (v j)=
      H j x (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (∑ i : I,∑ j : I,Q x i j • (flatOneRaisingL i (v j)+E i (flatTwoRaisingL j u)))=
      frameErrorMatrixRaisingCrossL L H Q x (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  simp only [frameErrorMatrixRaisingCrossL,map_sum,map_smul,map_add,
    _root_.sum_apply,_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => Q x i j • z)
  have hEA := DFunLike.congr_fun (hE i) (flatTwoRaisingL j u)
  have hA := DFunLike.congr_fun (flatThreeHalfRaisingL_high j) u
  simp only [ContinuousLinearMap.comp_apply] at hEA hA
  rw [flatOneRaisingL_half,hV j,hEA,← hA]

end ShrinkingSpheres
