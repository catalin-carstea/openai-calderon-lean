import Proof.CoarseRotationGraphCompletion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevRotationL_inclusion_apply (s t : ℝ) (hst : t ≤ s)
    (i j : I) (u : SphereSobolev s) :
    sphereSobolevRotationL t i j (sphereSobolevInclusionL s t hst u) =
      sphereSobolevInclusionL (s-1) (t-1) (by linarith) (sphereSobolevRotationL s i j u) := by
  apply sphereSobolev_ext (t-1)
  intro k
  rw [sphereSobolevCoefficientL_rotation,sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_rotation]

lemma sphereSobolevRotationL_one_inclusion_two (i j : I) (u : SphereSobolev 2) :
    sphereSobolevRotationL 1 i j (sphereSobolevInclusionL 2 1 (by norm_num) u) =
      sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevRotationL 2 i j u) := by
  simpa only [sphereSobolevInclusionL,show (1:ℝ)-1=0 by norm_num,show (2:ℝ)-1=1 by norm_num] using
    sphereSobolevRotationL_inclusion_apply 2 1 (by norm_num) i j u

/-- A right scalar multiplier product has the expected coarse rotation
    graph using only its H1 product rule and compatible bounded generators.
    No H2 multiplier witness is required. -/
theorem coarse_rotation_graph_comp_right_multiplier (i j : I)
    (A C : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hA : ∀ f : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (A (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+A (sphereSobolevRotationL 2 i j f)))
    (B1 D1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (B0 D0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (hB : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (B1 u) =
      B0 (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (hD : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (D1 u) =
      D0 (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (hProduct : ∀ u,sphereSobolevRotationL 1 i j (B1 u) =
      D0 (sphereSobolevInclusionL 1 0 (by norm_num) u)+B0 (sphereSobolevRotationL 1 i j u))
    (f : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j ((A.comp B1) (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        ((C.comp B1+A.comp D1) (sphereSobolevInclusionL 2 1 (by norm_num) f)+
          (A.comp B1) (sphereSobolevRotationL 2 i j f)) := by
  let u := sphereSobolevInclusionL 2 1 (by norm_num) f
  let v := D1 u+B1 (sphereSobolevRotationL 2 i j f)
  have hDomain : sphereSobolevRotationL 1 i j (B1 u) =
      sphereSobolevInclusionL 1 0 (by norm_num) v := by
    calc
      _ = D0 (sphereSobolevInclusionL 1 0 (by norm_num) u)+B0 (sphereSobolevRotationL 1 i j u) := hProduct u
      _ = D0 (sphereSobolevInclusionL 1 0 (by norm_num) u)+B0
          (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevRotationL 2 i j f)) := by
        rw [sphereSobolevRotationL_one_inclusion_two]
      _ = sphereSobolevInclusionL 1 0 (by norm_num) (D1 u)+
          sphereSobolevInclusionL 1 0 (by norm_num) (B1 (sphereSobolevRotationL 2 i j f)) :=
        congrArg₂ (fun a b : SphereSobolev 0 => a+b) (hD u).symm (hB _).symm
      _ = _ := (sphereSobolevInclusionL 1 0 (by norm_num)).map_add _ _ |>.symm
  have hh := coarse_rotation_distribution_of_H1_graph i j A C hA (B1 u) v hDomain
  simpa only [u,v,map_add,ContinuousLinearMap.comp_apply,_root_.add_apply,add_assoc] using hh

/-- Scalar multiplier compatibility and symmetry transport a true coarse
    adjunction through a right multiplier. -/
lemma coarse_pairing_comp_right_multiplier
    (A Aa : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (B1 : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (B0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (hA : ∀ u v,⟪A u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Aa v⟫_ℝ)
    (hB : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (B1 u) =
      B0 (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (hSym : ∀ u v,⟪B0 u,v⟫_ℝ = ⟪u,B0 v⟫_ℝ)
    (u v : SphereSobolev 1) :
    ⟪(A.comp B1) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,(B0.comp Aa) v⟫_ℝ := by
  exact (hA (B1 u) v).trans ((congrArg (fun w : SphereSobolev 0 => ⟪w,Aa v⟫_ℝ) (hB u)).trans (hSym _ _))

end ShrinkingSpheres
