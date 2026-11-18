import Proof.RelativeActualCovariantDerivative
import Proof.NativeRelativeForwardRotationGraph
import Proof.NativeRelativeAdjointRotationGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A global coarse operator derivative corrected by its actual angular
    connection action, interpreted in distributions on a common H2 core. -/
def CoarseCovariantRotationGraph (d : Data) (y a : X)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : Prop :=
  ∀ u : SphereSobolev 2,
    sphereSobolevInclusionL 0 (-1) (by norm_num) (S (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (fderiv ℝ H y a (sphereSobolevInclusionL 2 1 (by norm_num) u))-
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        (sphereSobolevRotationL 0 i j (H y (sphereSobolevInclusionL 2 1 (by norm_num) u))-
          sphereSobolevInclusionL 0 (-1) (by norm_num) (H y (sphereSobolevRotationL 2 i j u)))

lemma coarseCovariantRotationGraph_of_angular (d : Data) (y a : X)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (C : I → I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hJet : fderiv ℝ H y a-∑ i : I,∑ j : I,
      ((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • C i j = S)
    (hGraph : ∀ i j : I,∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (H y (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (C i j (sphereSobolevInclusionL 2 1 (by norm_num) u)+H y (sphereSobolevRotationL 2 i j u))) :
    CoarseCovariantRotationGraph d y a H S := by
  intro u
  have hv := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    sphereSobolevInclusionL 0 (-1) (by norm_num) (T (sphereSobolevInclusionL 2 1 (by norm_num) u))) hJet
  simp only [_root_.sub_apply,_root_.sum_apply,_root_.smul_apply,map_sub,map_sum,map_smul] at hv
  rw [← hv]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hGraph,map_add,add_sub_cancel_right]

theorem actual_covariant_rotation_graph_of_germ (d : Data) (y a : X)
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (F : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hGerm : H =ᶠ[𝓝 y] fun x => F (normalFrameRelativeActualParameter d (d.radius y) x))
    (hr : DifferentiableAt ℝ d.radius y) (hr0 : d.radius y ≠ 0)
    (hL : DifferentiableAt ℝ (frameVectorLinear d.frame) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => d.frame x i) y)
    (hframe : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j =
      -frameConnectionCoefficient d.γ d.frame y a j i)
    (hH : DifferentiableAt ℝ H y)
    (hF : DifferentiableAt ℝ F ((y,frameVectorLinear d.frame y),0))
    (hGraph : ∀ i j : I,∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (F ((y,frameVectorLinear d.frame y),0)
        (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (normalFrameRelativeAngularDerivative d.γ F i j ((y,frameVectorLinear d.frame y),0)
              (sphereSobolevInclusionL 2 1 (by norm_num) u)+
            F ((y,frameVectorLinear d.frame y),0) (sphereSobolevRotationL 2 i j u))) :
    CoarseCovariantRotationGraph d y a H
      (fderiv ℝ F ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeHorizontalField d.γ d.radius a ((y,frameVectorLinear d.frame y),0))) := by
  have hJet := fderiv_actual_germ_covariant_eq_normalized_horizontal d y a H F hGerm
    hr hr0 hL he hframe hSkew hH hF
  have hPoint : H y = F ((y,frameVectorLinear d.frame y),0) := by
    have hh := hGerm.eq_of_nhds
    rw [normalFrameRelativeActualParameter_point d y hr0] at hh
    exact hh
  apply coarseCovariantRotationGraph_of_angular d y a H _ _ hJet
  intro i j u
  rw [hPoint]
  exact hGraph i j u
end ShrinkingSpheres
