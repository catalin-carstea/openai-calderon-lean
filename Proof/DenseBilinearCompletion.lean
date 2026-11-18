import Proof.Archive.DenseRealLinearExtension
import Mathlib.Analysis.Normed.Module.Dual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.AnisotropicCalderon.DenseBilinearCompletion
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Complete a bilinear form in both variables through dense continuous
    inclusions, with its bound in the target norms. -/
theorem exists_extension (L : E →L[ℝ] F →L[ℝ] ℝ)
    (I : E →L[ℝ] G) (J : F →L[ℝ] H) (hI : DenseRange I) (hJ : DenseRange J)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ u v, |L u v| ≤ M*‖I u‖*‖J v‖) :
    ∃ Q : G →L[ℝ] StrongDual ℝ H,
      ‖Q‖ ≤ M ∧ ∀ u v, Q (I u) (J v) = L u v := by
  let ell (u : E) : StrongDual ℝ H := (L u).toLinearMap.extendOfNorm J.toLinearMap
  have hEllBound (u : E) (v : F) : ‖L u v‖ ≤ (M*‖I u‖)*‖J v‖ := by
    simpa only [Real.norm_eq_abs] using hBound u v
  have hGraph (u : E) (v : F) : ell u (J v) = L u v :=
    DenseRealLinearExtension.extendOfNorm_apply_dense (L u).toLinearMap J.toLinearMap
      hJ (M*‖I u‖) (hEllBound u) v
  have hNorm (u : E) : ‖ell u‖ ≤ M*‖I u‖ := by
    apply (ell u).opNorm_le_bound (by positivity)
    exact DenseRealLinearExtension.norm_extendOfNorm_apply_dense (L u).toLinearMap
      J.toLinearMap hJ (M*‖I u‖) (hEllBound u)
  let P : E →ₗ[ℝ] StrongDual ℝ H :=
    { toFun := ell
      map_add' := by
        intro u v
        apply ContinuousLinearMap.ext
        apply funext_iff.mp (hJ.equalizer (ell (u+v)).continuous (ell u+ell v).continuous ?_)
        funext w
        change ell (u+v) (J w) = (ell u+ell v) (J w)
        simp only [hGraph,_root_.add_apply,map_add]
      map_smul' := by
        intro c u
        apply ContinuousLinearMap.ext
        apply funext_iff.mp (hJ.equalizer (ell (c • u)).continuous (c • ell u).continuous ?_)
        funext w
        change ell (c • u) (J w) = (c • ell u) (J w)
        simp only [hGraph,_root_.smul_apply,map_smul,RingHom.id_apply] }
  let Q : G →L[ℝ] StrongDual ℝ H := P.extendOfNorm I.toLinearMap
  have hQ (u : E) : Q (I u) = P u :=
    DenseRealLinearExtension.extendOfNorm_apply_dense P I.toLinearMap hI M hNorm u
  refine ⟨Q,Q.opNorm_le_bound hM
    (DenseRealLinearExtension.norm_extendOfNorm_apply_dense P I.toLinearMap hI M hNorm),?_⟩
  intro u v
  rw [hQ]
  exact hGraph u v

end OAI.AnisotropicCalderon.DenseBilinearCompletion
