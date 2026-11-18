import Proof.ActualFrameCorrectionGraded
import Proof.MatrixCompositionBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- One shared first-order matrix cross, used for raising/F and scaled-degree/F. -/
def firstCorrectionMatrixCrossL (d : Data)
    (M : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,∑ j : I,Q x i j • ((M i x).comp (firstFrameAdjointCorrectionSobolevL d x j)+
    (firstFrameAdjointCorrectionL d x i).comp (M j x))

lemma norm_firstCorrectionMatrixCrossL_le (d : Data)
    (M : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : X → I → I → ℝ) (x : X)
    {B CA C0 C1 : ℝ} (hB : 0 ≤ B) (hCA : 0 ≤ CA) (hC0 : 0 ≤ C0)
    (hQ : ∀ i j,|Q x i j| ≤ B) (hM : ∀ i,‖M i x‖ ≤ CA)
    (hF0 : ∀ i,‖firstFrameAdjointCorrectionL d x i‖ ≤ C0)
    (hF1 : ∀ j,‖firstFrameAdjointCorrectionSobolevL d x j‖ ≤ C1) :
    ‖firstCorrectionMatrixCrossL d M Q x‖ ≤ 9*B*CA*(C1+C0) := by
  have hEq : firstCorrectionMatrixCrossL d M Q x=
      (∑ i : I,∑ j : I,Q x i j • (M i x).comp (firstFrameAdjointCorrectionSobolevL d x j))+
      (∑ i : I,∑ j : I,Q x i j • (firstFrameAdjointCorrectionL d x i).comp (M j x)) := by
    simp only [firstCorrectionMatrixCrossL,smul_add,Finset.sum_add_distrib]
  rw [hEq]
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_matrix_composition_sum_le (fun i => M i x) (firstFrameAdjointCorrectionSobolevL d x)
      (Q x) hB hCA hQ hM hF1)
    (norm_matrix_composition_sum_le (firstFrameAdjointCorrectionL d x) (fun j => M j x)
      (Q x) hB hC0 hQ hF0 hM)).trans_eq (by ring))

lemma firstCorrectionMatrixCrossL_sub (d : Data)
    (M : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Q R : X → I → I → ℝ) (x : X) :
    firstCorrectionMatrixCrossL d M Q x-firstCorrectionMatrixCrossL d M R x=
      firstCorrectionMatrixCrossL d M (fun x i j => Q x i j-R x i j) x := by
  simp only [firstCorrectionMatrixCrossL,sub_smul,Finset.sum_sub_distrib]

lemma firstCorrectionMatrixCrossL_delta (d : Data)
    (M : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (x : X) :
    firstCorrectionMatrixCrossL d M (fun _x i j => if i=j then 1 else 0) x=
      ∑ i : I,((M i x).comp (firstFrameAdjointCorrectionSobolevL d x i)+
        (firstFrameAdjointCorrectionL d x i).comp (M i x)) := by
  simp only [firstCorrectionMatrixCrossL,ite_smul,one_smul,zero_smul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma Admissible.contDiffOn_firstCorrectionMatrixCrossL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {Mj : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ Mj Cj floor ε d) (hK : 0 < K)
    (M : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : X → I → I → ℝ)
    (hM : ∀ i,ContDiffOn ℝ ∞ (M i) Y) (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => Q x i j) Y) :
    ContDiffOn ℝ ∞ (firstCorrectionMatrixCrossL d M Q) Y := by
  have hF1 (i : I) : ContDiffOn ℝ ∞ (fun x => firstFrameAdjointCorrectionSobolevL d x i) Y :=
    hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK 1 i
  have hF0 (i : I) : ContDiffOn ℝ ∞ (fun x => firstFrameAdjointCorrectionL d x i) Y := by
    simpa only [firstFrameAdjointCorrectionAtL_zero] using
      hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK 0 i
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hQ i j).smul
    (((hM i).clm_comp (hF1 j)).add ((hF0 i).clm_comp (hM j)))))
end ShrinkingSpheres
