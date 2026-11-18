import Proof.SphereSobolevOperatorExt
import Proof.Archive.SphereSobolevBesselOrderCompatibility
import Proof.FiniteJetBudgetAlgebra
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

def halfDegreeHigherLift
    (R S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (sphereSobolevBesselOrderL (-(1/2:ℝ)) (1/2:ℝ)).comp
    (R.comp (sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ))+
      S.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))

lemma sphereSobolevBesselOrderL_threeHalf_single (n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevBesselOrderL (3/2:ℝ) (1/2:ℝ) (sphereSobolevSingleL (3/2:ℝ) n z) =
      (1+(n:ℝ)) • sphereSobolevSingleL (1/2:ℝ) n z := by
  apply sphereSobolev_ext (1/2:ℝ)
  intro k
  rw [sphereSobolevCoefficientL_besselOrder,map_smul]
  by_cases hkn : k=n
  · subst k
    simp only [sphereSobolevCoefficientL_single_self]
    congr 1
    norm_num [besselWeight]
  · simp only [sphereSobolevCoefficientL_single_ne _ _ _ hkn,smul_zero]

/-- A controlled degree commutator upgrades the SAME half-order operator
    by one angular derivative. The construction is linear in both inputs. -/
lemma halfDegreeHigherLift_single_coefficient
    (R S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hS : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) m
          (R (sphereSobolevSingleL (1/2:ℝ) n z)))
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (1/2:ℝ) m
      (halfDegreeHigherLift R S (sphereSobolevSingleL (3/2:ℝ) n z)) =
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (R (sphereSobolevSingleL (1/2:ℝ) n z)) := by
  simp only [halfDegreeHigherLift,ContinuousLinearMap.comp_apply,_root_.add_apply,
    sphereSobolevCoefficientL_besselOrder,map_add,sphereSobolevBesselOrderL_threeHalf_single,
    sphereSobolevInclusionL_single,map_smul,hS]
  simp only [smul_smul]
  rw [← add_smul]
  have hW : (1+(n:ℝ))*besselWeight ((-(1/2:ℝ))-(1/2:ℝ)) m+
      besselWeight ((-(1/2:ℝ))-(1/2:ℝ)) m*((m:ℝ)-(n:ℝ)) = 1 := by
    rw [show (-(1/2:ℝ))-(1/2:ℝ) = -1 by norm_num]
    simp only [besselWeight,Real.rpow_neg_one]
    field_simp [show (1+(m:ℝ)) ≠ 0 by positivity]
    <;> ring
  rw [hW,one_smul]

lemma halfDegreeHigherLift_inclusion
    (R S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hS : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) m
          (R (sphereSobolevSingleL (1/2:ℝ) n z))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (halfDegreeHigherLift R S) =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply sphereSobolev_clm_ext_on_single (3/2:ℝ)
  intro n z
  apply sphereSobolev_ext (-(1/2:ℝ))
  intro m
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,sphereSobolevInclusionL_single]
  exact halfDegreeHigherLift_single_coefficient R S hS m n z

lemma norm_halfDegreeHigherLift_le
    (R S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :
    ‖halfDegreeHigherLift R S‖ ≤ ‖R‖+‖S‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_sphereSobolevBesselOrderL_le _ _) (norm_add_le _ _)
      (norm_nonneg _) zero_le_one).trans (by
      simp only [one_mul]
      exact add_le_add
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (norm_sphereSobolevBesselOrderL_le _ _) (norm_nonneg _)).trans_eq (mul_one _)))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (mul_one _)))))
end OAI.AnisotropicCalderon.SphereHarmonic
