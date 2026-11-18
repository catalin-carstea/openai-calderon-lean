import Proof.MatrixCompositionBound
import Proof.ActualFrameErrorEndpointPair
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A smooth actual H1 lift of the coarse output is the SAME higher endpoint
    after its genuine inclusion into H(1/2). -/
lemma higher_endpoint_actual_lift
    (E : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hH : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H=
      E.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (u : SphereSobolev 2) (v : SphereSobolev 1)
    (hOut : sphereSobolevInclusionL 1 0 (by norm_num) v=E (sphereSobolevInclusionL 2 1 (by norm_num) u)) :
    sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v=
      H (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  have hh := DFunLike.congr_fun hH (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply] at hh
  rw [sphereSobolevInclusionL_trans_apply] at hh
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [sphereSobolevInclusionL_trans_apply]
  exact hOut.trans hh.symm

namespace ActualFrameErrorEndpointPair
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {CE : ℝ}

def productL (P : ActualFrameErrorEndpointPair Y d A G CE) (Q : X → I → I → ℝ) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,∑ j : I,Q x i j • (P.low i x).comp (P.high j x)

lemma product_smooth (P : ActualFrameErrorEndpointPair Y d A G CE) (Q : X → I → I → ℝ)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => Q x i j) Y) :
    ContDiffOn ℝ ∞ (P.productL Q) Y := by
  exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (hQ i j).smul ((P.low_smooth i).clm_comp (P.high_smooth j))))

lemma norm_productL_le (P : ActualFrameErrorEndpointPair Y d A G CE)
    (Q : X → I → I → ℝ) {B : ℝ} (hB : 0 ≤ B) (hCE : 0 ≤ CE)
    {x : X} (hx : x ∈ Y) (hr : 0 ≤ d.radius x) (hQ : ∀ i j,|Q x i j| ≤ B) :
    ‖P.productL Q x‖ ≤ 9*B*CE^2*(d.radius x)^2 := by
  exact (norm_matrix_composition_sum_le (fun i => P.low i x) (fun j => P.high j x)
    (Q x) hB (mul_nonneg hCE hr) hQ
    (fun i => P.low_bound i x hx) (fun j => P.high_bound j x hx)).trans_eq (by ring)

/-- The graded controlled product is exactly the actual two-error composition
    on arbitrary smooth H1 output lifts of the SAME physical coarse errors. -/
lemma product_actual_lifts (P : ActualFrameErrorEndpointPair Y d A G CE)
    (Q : X → I → I → ℝ) {x : X} (hx : x ∈ Y) (u : SphereSobolev 2)
    (v : I → SphereSobolev 1)
    (hOut : ∀ j,sphereSobolevInclusionL 1 0 (by norm_num) (v j)=
      actualFrameFirstAdjointErrorFamily d A G j x (sphereSobolevInclusionL 2 1 (by norm_num) u)) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (∑ i : I,∑ j : I,Q x i j • actualFrameFirstAdjointErrorFamily d A G i x (v j))=
        P.productL Q x (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  simp only [productL,map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => Q x i j • z)
  have hLow := DFunLike.congr_fun (P.low_coarse i x hx) (v j)
  simp only [ContinuousLinearMap.comp_apply] at hLow
  rw [hLow,higher_endpoint_actual_lift _ _ (P.high_coarse j x hx) u (v j) (hOut j)]
end ActualFrameErrorEndpointPair
end ShrinkingSpheres
