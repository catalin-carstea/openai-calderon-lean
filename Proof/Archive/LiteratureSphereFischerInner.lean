/- Adopted from the selected ZIP, lean/Calderon/LiteratureSphereFischerInner.lean.
   Proof bodies and declarations are preserved. Local import paths are rewritten.
-/
import Proof.Archive.LiteratureSphereIntegrals

 




namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

theorem sphereFischerInner : SphereFischerInner := by
  intro k p q hp hq
  have hG := gaussPair_eq_sphere hp.1 hq.1
  rw [gaussPair_eq_fischer hp hq, gamma_half_odd] at hG
  have hσ := surface_mul_gamma
  have hΓ : 0 < Real.Gamma (3 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hN : 0 < sphereNormalization 3 k := Finset.prod_pos fun j _ => by positivity
  have hπ : 0 < Real.pi ^ ((3 : ℝ) / 2) := by positivity
  have hS : 0 < (surfaceMeasure Set.univ).toReal := by
    have := hσ ▸ hπ
    nlinarith [this]
  rw [sphereInner_eq, normalizedFischerInner, Fintype.card_fin]
  set I := ∫ ω : UnitSphere, pq p q ω ∂surfaceMeasure
  field_simp
  rw [← hσ] at hG
  field_simp at hG
  nlinarith [hG, hΓ, hS, hN]

end OAI.AnisotropicCalderon.SphereHarmonic
