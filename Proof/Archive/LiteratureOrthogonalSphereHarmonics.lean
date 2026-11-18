/- Adopted from the selected ZIP, lean/Calderon/LiteratureOrthogonalSphereHarmonics.lean.
   Proof declarations and bodies are preserved; local import paths are rewritten. -/
import Proof.Archive.LiteratureSphereIntegrals

 



namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

theorem orthogonalSphereHarmonics : OrthogonalSphereHarmonics := by
  intro k m hkm u hu v hv
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hu
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hv
  have hG := gaussPair_eq_sphere hp.1 hq.1
  rw [gaussPair_eq_zero hkm hp hq] at hG
  have hΓ : 0 < Real.Gamma ((((k + m : ℕ) : ℝ) + 3) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hI : ∫ ω : UnitSphere, pq p q ω ∂surfaceMeasure = 0 := by
    rcases mul_eq_zero.mp hG.symm with h | h
    · exact h
    · linarith [div_pos hΓ two_pos]
  rw [sphereInner_eq, hI, mul_zero]

end OAI.AnisotropicCalderon.SphereHarmonic
