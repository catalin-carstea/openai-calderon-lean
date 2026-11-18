import Proof.CovariantHalfCoarseBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def frameAngularConnectionFiveHalfL (d : Data) (y a : X) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL (5/2:ℝ) i j

def higherOperatorCovariantDerivativeL (d : Data)
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X) :
    SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      ((fderiv ℝ H y a).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))-
    (frameAngularConnectionHalfL d y a).comp
      ((H y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))+
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      ((H y).comp (frameAngularConnectionFiveHalfL d y a))

lemma frame_connection_five_half_coarse (d : Data) (y a : X) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (frameAngularConnectionFiveHalfL d y a u)=
      ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        sphereSobolevRotationL 2 i j (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) u) := by
  simp only [frameAngularConnectionFiveHalfL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [sphereSobolevInclusionL,show (5/2:ℝ)-1=3/2 by norm_num,show (2:ℝ)-1=1 by norm_num] using
    (sphereSobolevRotationL_inclusion_apply (5/2:ℝ) 2 (by norm_num) i j u).symm

/-- A genuine HIGH first-jet square of the SAME coarse S gives the exact
higher covariant derivative on a genuine H5/2 core. This is an endpoint
bridge; the HIGH witness and its norm remain explicit inputs. -/
theorem higher_covariant_derivative_of_coarse {d : Data} {y a : X}
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hF : DifferentiableAt ℝ F y) (hH : DifferentiableAt ℝ H y)
    (hHigh : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H x)=
      (F x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hGraph : CoarseCovariantRotationGraph d y a F S)
    (hJet : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp N=
      S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    higherOperatorCovariantDerivativeL d H y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (N.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) := by
  have hAt := hHigh.self_of_nhds
  have hD := compatible_endpoint_fderiv H F
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) y a hH hF hHigh
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (-(1/2:ℝ)) (-1:ℝ) (by norm_num)
  have hDer := congrArg (sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num))
    (DFunLike.congr_fun hD (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u))
  have hOut := DFunLike.congr_fun hAt (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
  have hN := DFunLike.congr_fun hJet (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at hDer hOut hN
  have hC1 := frameAngularConnectionHalfL_lower_coarse d y a
    (H y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u))
  rw [hOut] at hC1
  have hC2 := DFunLike.congr_fun hAt (frameAngularConnectionFiveHalfL d y a u)
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,frame_connection_five_half_coarse] at hC2
  have hC2' := congrArg (sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num)) hC2
  simp only [sphereSobolevInclusionL_trans_apply,map_sum,map_smul] at hC2'
  have hN' := congrArg (sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num)) hN
  simp only [sphereSobolevInclusionL_trans_apply] at hN'
  have hG := hGraph (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) u)
  simp only [sphereSobolevInclusionL_trans_apply] at hG
  simp only [higherOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,_root_.add_apply,
    _root_.sub_apply,map_add,map_sub,sphereSobolevInclusionL_trans_apply]
  refine (congrArg₂ (fun x z : SphereSobolev (-1:ℝ) => x+z)
    (congrArg₂ (fun x z : SphereSobolev (-1:ℝ) => x-z) hDer hC1) hC2').trans ?_
  simp only [smul_sub,Finset.sum_sub_distrib] at hG
  convert hG.symm.trans hN'.symm using 1 <;> abel

end ShrinkingSpheres.ParallelEnergy
