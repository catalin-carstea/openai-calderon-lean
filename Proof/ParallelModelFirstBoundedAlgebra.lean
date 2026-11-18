import Proof.ParallelScalarModelDefectProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Pure endpoint norm algebra for a bounded remainder against a model
quadratic word. The genuine geometric graphs are supplied by its caller. -/
lemma model_first_bounded_zero_pair_norm
    (R : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (D J : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Kf : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Ka : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (u h : SphereSobolev (3/2:ℝ)) (R0 CF CA ε β : ℝ)
    (hR0 : 0 ≤ R0) (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hR : ‖R‖ ≤ R0) (hD : ‖D‖ ≤ 2) (hF : ‖Kf‖ ≤ CF*ε/β^2) (hA : ‖Ka‖ ≤ CA*ε/β^2) :
    |sphereSobolevDualPairing (1/2:ℝ) (Kf (J h)) (R (D u))-
      sphereSobolevDualPairing (1/2:ℝ) (J h) (R (D (Ka u)))| ≤
      (2*R0*(CF+CA))*ε/β^2*‖u‖*‖J h‖ := by
  have hRD (v : SphereSobolev (3/2:ℝ)) : ‖R (D v)‖ ≤ 2*R0*‖v‖ :=
    ((R.le_opNorm _).trans (mul_le_mul hR ((D.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _))) (norm_nonneg _) hR0)).trans_eq (by ring)
  have hFN : ‖Kf (J h)‖ ≤ (CF*ε/β^2)*‖J h‖ :=
    (Kf.le_opNorm _).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg _))
  have hAN : ‖Ka u‖ ≤ (CA*ε/β^2)*‖u‖ :=
    (Ka.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hP1 : |sphereSobolevDualPairing (1/2:ℝ) (Kf (J h)) (R (D u))| ≤ (2*R0*CF)*ε/β^2*‖u‖*‖J h‖ := by
    calc
      _ ≤ ‖Kf (J h)‖*‖R (D u)‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ((CF*ε/β^2)*‖J h‖)*(2*R0*‖u‖) := mul_le_mul hFN (hRD u) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hP2 : |sphereSobolevDualPairing (1/2:ℝ) (J h) (R (D (Ka u)))| ≤ (2*R0*CA)*ε/β^2*‖u‖*‖J h‖ := by
    calc
      _ ≤ ‖J h‖*‖R (D (Ka u))‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖J h‖*((2*R0)*((CA*ε/β^2)*‖u‖)) := mul_le_mul_of_nonneg_left
        ((hRD (Ka u)).trans (mul_le_mul_of_nonneg_left hAN (mul_nonneg (by norm_num) hR0))) (norm_nonneg _)
      _ = _ := by ring
  exact ((abs_sub _ _).trans (add_le_add hP1 hP2)).trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
