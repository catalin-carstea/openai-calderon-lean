import Proof.HalfScalarTransposeCompatibility
import Proof.FirstCommutatorFormBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine half graphs identify physical inner products with the SAME
low transpose; no Sobolev regularity is inferred from carrier equality. -/
lemma first_half_adjoint_pair_eq_physical_inner
    (B : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
      B.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u : SphereSobolev (3/2:ℝ)) (z : SphereSobolev (1/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (B.adjoint z)=
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (H u),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) z⟫_ℝ := by
  have h := DFunLike.congr_fun hH u
  simp only [ContinuousLinearMap.comp_apply] at h
  unfold sphereSobolevDualPairing
  rw [B.adjoint_inner_right,real_inner_comm]
  change sphereSobolevDualPairing (1/2:ℝ) z
    (B (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=_
  rw [←h,half_dual_pairing_inclusion,real_inner_comm]

/-- One actual angular commutator row is the forward physical product
minus its crossed true-adjoint product. -/
lemma first_leading_row_commutator_identity
    (Bb Bc : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hb Hc Ab Ac : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Kbc : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hHb : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hb=
      Bb.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hAc : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ac=
      Bc.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hComm : Bb.adjoint.comp Hc-Bc.comp Ab=
      Kbc.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u v : SphereSobolev (3/2:ℝ)) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (Hb u),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (Hc v)⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
        (Kbc (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v))+
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (Ab v),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (Ac u)⟫_ℝ := by
  have h := DFunLike.congr_fun hComm v
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply] at h
  have hPair := first_half_adjoint_pair_eq_physical_inner Bb Hb hHb u (Hc v)
  have hCross := first_half_adjoint_pair_eq_physical_inner Bc.adjoint Ac hAc u (Ab v)
  rw [ContinuousLinearMap.adjoint_adjoint] at hCross
  have hPoint : Bb.adjoint (Hc v)=
      Kbc (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)+Bc (Ab v) := by
    exact sub_eq_iff_eq_add.mp h
  rw [hPoint] at hPair
  simp only [sphereSobolevDualPairing,inner_add_right] at hPair hCross ⊢
  rw [hCross] at hPair
  exact hPair.symm.trans (congrArg (fun z : ℝ =>
    ⟪sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u,
      Kbc (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)⟫_ℝ+z)
    (real_inner_comm _ _))

/-- The leading forward square equals a controlled commutator form plus
crossed true-adjoint rows. Their subsequent base exchange must stay paired. -/
theorem first_forward_square_eq_commutator_cross
    (B : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (K : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hH : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H b)=
      (B b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hA : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A b)=
      (B b).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hComm : ∀ b c,(B b).adjoint.comp (H c)-(B c).comp (A b)=
      (K b c).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (V : I → SphereSobolev (3/2:ℝ)) :
    ‖∑ b : I,sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (H b (V b))‖^2=
      firstCommutatorForm K (fun b => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V b))+
      ∑ b : I,∑ c : I,⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (A b (V c)),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (A c (V b))⟫_ℝ := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum]
  simp_rw [first_leading_row_commutator_identity _ _ _ _ _ _ _ (hH _) (hA _) (hComm _ _)]
  simp only [Finset.sum_add_distrib,firstCommutatorForm]
  congr 1 <;> exact Finset.sum_comm

end ShrinkingSpheres.ParallelEnergy
