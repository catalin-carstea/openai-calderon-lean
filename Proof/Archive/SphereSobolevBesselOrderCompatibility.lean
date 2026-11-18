import Proof.Archive.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SpectralWeightedGraph

 
def sphereSobolevBesselOrderL (s t : ℝ) :
    SphereSobolev s →L[ℝ] SphereSobolev t :=
  (sphereSobolevBesselEquiv s (s-t)).toContinuousLinearEquiv.toContinuousLinearMap

lemma sphereSobolevCoefficientL_besselOrder (s t : ℝ) (u : SphereSobolev s) (k : ℕ) :
    sphereSobolevCoefficientL t k (sphereSobolevBesselOrderL s t u) =
      besselWeight (s-t) k • sphereSobolevCoefficientL s k u := by
  change besselWeight (-t) k • u k =
    besselWeight (s-t) k • (besselWeight (-s) k • u k)
  rw [smul_smul]
  congr 1
  unfold besselWeight
  rw [← Real.rpow_add (by positivity : 0 < 1+(k:ℝ))]
  congr 1
  ring

lemma norm_sphereSobolevBesselOrderL_le (s t : ℝ) :
    ‖sphereSobolevBesselOrderL s t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖u‖ ≤ 1*‖u‖
  exact (one_mul ‖u‖).symm.le

lemma sphereSobolevBesselOrderL_inverse (s t : ℝ) :
    (sphereSobolevBesselOrderL t s).comp (sphereSobolevBesselOrderL s t) =
      ContinuousLinearMap.id ℝ (SphereSobolev s) := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

lemma sphereSobolevBesselOrderL_inclusion_comp (s t q r : ℝ)
    (hts : t ≤ s) (hrq : r ≤ q) (h : s-q=t-r) :
    (sphereSobolevInclusionL q r hrq).comp (sphereSobolevBesselOrderL s q) =
      (sphereSobolevBesselOrderL t r).comp (sphereSobolevInclusionL s t hts) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolev_ext r
  intro k
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,
    sphereSobolevCoefficientL_besselOrder,h]

lemma besselWeight_neg_mul_self (a : ℝ) (k : ℕ) :
    besselWeight (-a) k * besselWeight a k = 1 := by
  simpa only [besselWeight,neg_add_cancel,Real.rpow_zero] using
    (Real.rpow_add (by positivity : 0 < 1+(k:ℝ)) (-a) a).symm

end OAI.AnisotropicCalderon.SphereHarmonic
