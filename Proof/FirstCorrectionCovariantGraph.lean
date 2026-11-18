import Proof.OrderZeroCovariantGraph
import Proof.FirstAdjointCorrectionHorizontal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The genuine coarse realization of the bounded first frame correction. -/
def firstFrameCorrectionCoarseFamily (d : Data) (j : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (firstFrameAdjointCorrectionL d x j).comp (sphereSobolevInclusionL 1 0 (by norm_num))

lemma Admissible.firstFrameCorrectionCoarseFamily_covariant_graph {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a : X) (j : I) :
    CoarseCovariantRotationGraph d y a (firstFrameCorrectionCoarseFamily d j)
      ((∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • firstFrameCorrectionCoarseFamily d k y)+
        (firstFrameAdjointCovariantJetL d y a j).comp (sphereSobolevInclusionL 1 0 (by norm_num))) := by
  have hB := coarseCovariantRotationGraph_of_orderZero d y a
    (fun x => firstFrameAdjointCorrectionL d x j) (firstFrameAdjointCorrectionSobolevL d y j)
    (firstFrameAdjointCorrectionL_coarse d y j)
    (((hd.contDiffOn_firstFrameAdjointCorrectionL hY hΩ hK j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hJ := hd.firstFrameAdjointHorizontalCommutatorL_eq hY hΩ hK hy a j
  have hConn : (∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • firstFrameAdjointCorrectionL d y k).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)) =
      ∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • firstFrameCorrectionCoarseFamily d k y := by
    apply DFunLike.ext
    intro u
    simp only [firstFrameCorrectionCoarseFamily,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply]
  change ((fderiv ℝ (fun x => firstFrameAdjointCorrectionL d x j) y a).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))+
    (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)).comp (firstFrameAdjointCorrectionSobolevL d y j)-
    (firstFrameAdjointCorrectionL d y j).comp (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)))-
    (∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • firstFrameAdjointCorrectionL d y k).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)) = _ at hJ
  rw [hConn] at hJ
  have hEq := (sub_eq_iff_eq_add).mp hJ
  have hEq' := hEq.trans (add_comm _ _)
  exact hEq' ▸ hB
end ShrinkingSpheres
