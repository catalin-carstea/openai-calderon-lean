import Proof.GradedRotationThreeComm
import Proof.OneSectionCovariantDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def threeRotationMapL (s : ℝ) :
    (I → ℝ) →L[ℝ] SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  (ContinuousLinearMap.proj 0).smulRight (sphereSobolevRotationL s 0 1)+
    (ContinuousLinearMap.proj 1).smulRight (sphereSobolevRotationL s 0 2)+
    (ContinuousLinearMap.proj 2).smulRight (sphereSobolevRotationL s 1 2)

lemma threeRotationMapL_apply (s : ℝ) (p : I → ℝ) : threeRotationMapL s p=threeRotationL s p := by
  simp only [threeRotationMapL,threeRotationL,_root_.add_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

lemma threeRotationL_one_inclusion_two (p : I → ℝ) :
    (sphereSobolevInclusionL 1 0 (by norm_num)).comp (threeRotationL 2 p)=
      (threeRotationL 1 p).comp (sphereSobolevInclusionL 2 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [threeRotationL,ContinuousLinearMap.comp_apply,_root_.add_apply,
    _root_.smul_apply,map_add,map_smul,sphereSobolevRotationL_one_inclusion_two]

lemma fderiv_threeRotationL (s : ℝ) (p : X → I → ℝ) (y a : X)
    (hp : DifferentiableAt ℝ p y) :
    fderiv ℝ (fun x => threeRotationL s (p x)) y a=threeRotationL s (fderiv ℝ p y a) := by
  have h := (threeRotationMapL s).hasFDerivAt.comp y hp.hasFDerivAt
  simpa only [Function.comp_def,threeRotationMapL_apply,ContinuousLinearMap.comp_apply]
    using DFunLike.congr_fun h.fderiv a

lemma norm_threeRotationL_le (s : ℝ) (p : I → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hp : ∀ i,|p i| ≤ B) : ‖threeRotationL s p‖ ≤ 3*Real.sqrt 2*B := by
  have h (i j k : I) : ‖p k • sphereSobolevRotationL s i j‖ ≤ B*Real.sqrt 2 := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hp k) (norm_sphereSobolevRotationL_le s i j) (norm_nonneg _) hB
  unfold threeRotationL
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add (h 0 1 0) (h 0 2 1)) (h 1 2 2)).trans_eq (by ring))

end ShrinkingSpheres
