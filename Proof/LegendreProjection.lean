import Proof.ZonalReproduction

noncomputable section
set_option autoImplicit false
open MvPolynomial MeasureTheory Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma unitSphere_sum_sq (w : UnitSphere) : ∑ i : I, (w.val i)^2 = 1 := by
  simpa [radiusSq] using eval_radiusSq_unitSphere w

/-- The probability-sphere Legendre kernel acts as the identity on the selected harmonic
    degree and as zero on every other harmonic degree. -/
theorem sphere_legendre_projection (w : UnitSphere) (m k : ℕ) (p : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    (2*(m : ℝ)+1) * (∫ z : UnitSphere, legendre (∑ i, w.val i*z.val i) m * eval (z.val : I → ℝ) p ∂sphereProbability) =
      if m = k then eval (w.val : I → ℝ) p else 0 := by
  have hZ : zonalPolynomial (w.val : I → ℝ) m ∈ harmonicHomogeneous m :=
    ⟨zonalPolynomial_homogeneous _ m, zonalPolynomial_harmonic _ (unitSphere_sum_sq w) m⟩
  have hI := polynomialSphereL2_inner (zonalPolynomial (w.val : I → ℝ) m) p
  simp_rw [eval_zonalPolynomial_unitSphere] at hI
  rw [← hI]
  by_cases hmk : m = k
  · subst k
    rw [if_pos rfl, sphereFischerInner m _ p hZ ⟨hp,hΔ⟩]
    simp only [normalizedFischerInner, Fintype.card_fin, fischerInner_zonalPolynomial _ m p hp hΔ,
      sphereNormalization_three_one]
    have hF : sphereNormalization 1 m ≠ 0 := (sphereNormalization_pos (by norm_num : 0 < 1) m).ne'
    have hM : 2*(m : ℝ)+1 ≠ 0 := by positivity
    field_simp [hF,hM]
  · rw [if_neg hmk, orthogonalSphereHarmonics m k hmk _ (polynomialSphereL2_mem m _ hZ)
      _ (polynomialSphereL2_mem k p ⟨hp,hΔ⟩), mul_zero]

end ShrinkingSpheres
