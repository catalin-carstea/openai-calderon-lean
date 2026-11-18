import Proof.NegativeHalfTransposeGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
local instance skewNegativeHalfComplete : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := lp.completeSpace
lemma negative_skew_half_compatible (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hSkew : ∀ u v : SphereSobolev 1,
      ⟪T u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        -⟪sphereSobolevInclusionL 1 0 (by norm_num) u,T v⟫_ℝ)
    (hGraph : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
      KN.comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))=
      KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  let KH : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := -KN.adjoint
  have hPair : ∀ u v : SphereSobolev 1,
      ⟪T u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,(-T) v⟫_ℝ := by
    intro u v
    simpa only [_root_.neg_apply,inner_neg_right] using hSkew u v
  have ht := negative_half_transpose_graph T (-T) KN hPair hGraph
  have hHalf : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (KH.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=T := by
    simpa only [KH,ContinuousLinearMap.neg_comp,ContinuousLinearMap.comp_neg,neg_neg] using congrArg Neg.neg ht
  have hc : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH=
      KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
    have hTest (u : SphereSobolev 1) :
        sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
          (KH (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))=
        KN (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
          (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) := by
      have hh := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u) hHalf
      have hn := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u) hGraph
      calc
        _ = sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
              (KH (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))) :=
          (sphereSobolevInclusionL_trans_apply _ _ _ _ _ _).symm
        _ = sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (T u) := congrArg _ hh
        _ = KN (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num) u) := hn
        _ = _ := congrArg KN (sphereSobolevInclusionL_trans_apply _ _ _ _ _ _).symm
    have he := (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)).equalizer
      ((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp KH).continuous
      (KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))).continuous (funext hTest)
    exact ContinuousLinearMap.ext (congrFun he)
  exact hc
end ShrinkingSpheres
