import Proof.CoarseDegreeDualForm
import Proof.Archive.SphereSobolevFinitePhysicalHalfDualPackets
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
 
attribute [local irreducible] sphereSobolevSingleL sphereSobolevCoefficientL sphereSobolevInclusionL

lemma finite_coarse_dual_degree_pair_bound_of_decoded_form_bound
    (T : SphereSobolev (2:ℝ) →L[ℝ] SphereSobolev (-1:ℝ))
    (K : ∀ m n : ℕ, harmonicSphereSubspace n →L[ℝ] harmonicSphereSubspace m)
    (hCoefficients : ∀ m n : ℕ, ∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-1:ℝ) m (T (sphereSobolevSingleL (2:ℝ) n z)) = ((m:ℝ)-(n:ℝ)) • K m n z)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ ncut : ℕ, ∀ u v : ∀ l, harmonicSphereSubspace l,
      |∑ m ∈ Finset.range ncut, ∑ n ∈ Finset.range ncut, ((m:ℝ)-(n:ℝ))*⟪K m n (u n),v m⟫_ℝ| ≤
        M*Real.sqrt (∑ l ∈ Finset.range ncut, (1+(l:ℝ))*‖u l‖^2)*Real.sqrt (∑ l ∈ Finset.range ncut, (1+(l:ℝ))*‖v l‖^2)) :
    ∀ u ∈ sphereSobolevFiniteSupport (2:ℝ),
      ∀ v ∈ sphereSobolevFiniteSupport 1, |sphereSobolevDualPairing 1 v (T u)| ≤ M*‖sphereSobolevInclusionL (2:ℝ) (1/2:ℝ) (by norm_num) u‖*‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v‖ := by
  let I := sphereSobolevInclusionL (2:ℝ) (1/2:ℝ) (by norm_num)
  intro u hu v hv
  obtain ⟨nu,hnu⟩ := hu
  obtain ⟨nv,hnv⟩ := hv
  let ncut := max nu nv
  have hU (k : ℕ) (hk : ncut ≤ k) : sphereSobolevCoefficientL (2:ℝ) k u = 0 := hnu k ((le_max_left nu nv).trans hk)
  have hV (k : ℕ) (hk : ncut ≤ k) : sphereSobolevCoefficientL 1 k v = 0 := hnv k ((le_max_right nu nv).trans hk)
  have hI (k : ℕ) (hk : ncut ≤ k) : sphereSobolevCoefficientL (1/2:ℝ) k (I u) = 0 :=
    (sphereSobolevCoefficientL_inclusion (2:ℝ) (1/2:ℝ) (by norm_num) u k).trans (hU k hk)
  have hNormU := sqrt_half_finite_decoded_eq_norm ncut (I u) hI
  have hInputNorm : Real.sqrt (∑ k ∈ Finset.range ncut, (1+(k:ℝ))*‖sphereSobolevCoefficientL (2:ℝ) k u‖^2) = ‖I u‖ := by
    simpa only [I,sphereSobolevCoefficientL_inclusion] using hNormU
  let J := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  have hJ (k : ℕ) (hk : ncut ≤ k) : sphereSobolevCoefficientL (1/2:ℝ) k (J v) = 0 :=
    (sphereSobolevCoefficientL_inclusion 1 (1/2:ℝ) (by norm_num) v k).trans (hV k hk)
  have hTestNorm : Real.sqrt (∑ k ∈ Finset.range ncut,
      (1+(k:ℝ))*‖sphereSobolevCoefficientL 1 k v‖^2) = ‖J v‖ := by
    simpa only [J,sphereSobolevCoefficientL_inclusion] using
      sqrt_half_finite_decoded_eq_norm ncut (J v) hJ
  have hDegree := hBound ncut (fun n => sphereSobolevCoefficientL (2:ℝ) n u) (fun m => sphereSobolevCoefficientL 1 m v)
  rw [hInputNorm,hTestNorm] at hDegree
  exact (congrArg abs (sphereSobolev_finite_coarse_dual_degree_form_of_coefficients T K hCoefficients ncut u v hU hV)).trans_le hDegree

end OAI.AnisotropicCalderon.SphereHarmonic
