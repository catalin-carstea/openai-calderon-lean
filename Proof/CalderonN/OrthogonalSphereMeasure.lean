module

public import Proof.CalderonN.SphereHarmonicBridge
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

/- Adopted from the selected ZIP, lean/Calderon/OrthogonalSphereMeasure.lean.
   Complete generic module; proof bodies preserved, local imports rewritten.
-/
noncomputable section
open MeasureTheory Set
open scoped Pointwise
namespace OAI.AnisotropicCalderon.OrthogonalSphereMeasure
open SphereHarmonic CalderonN

variable {n : ℕ}

theorem orthogonal_mem_sphere (T : X n ≃ₗᵢ[ℝ] X n) (u : UnitSphere n) :
    T u.val ∈ Metric.sphere (0 : X n) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, T.norm_map]
  exact mem_sphere_zero_iff_norm.mp u.property

def orthogonalSphereHomeomorph (T : X n ≃ₗᵢ[ℝ] X n) : UnitSphere n ≃ₜ UnitSphere n where
  toFun u := ⟨T u.val, orthogonal_mem_sphere T u⟩
  invFun u := ⟨T.symm u.val, orthogonal_mem_sphere T.symm u⟩
  left_inv u := Subtype.ext (T.symm_apply_apply u.val)
  right_inv u := Subtype.ext (T.apply_symm_apply u.val)
  continuous_toFun := (T.continuous.comp continuous_subtype_val).subtype_mk
    (orthogonal_mem_sphere T)
  continuous_invFun := (T.symm.continuous.comp continuous_subtype_val).subtype_mk
    (orthogonal_mem_sphere T.symm)

lemma orthogonalSphereHomeomorph_apply_val (T : (CalderonN.X n) ≃ₗᵢ[ℝ] (CalderonN.X n)) (u : (UnitSphere n)) :
    (orthogonalSphereHomeomorph T u).val = T u.val := rfl

lemma orthogonalSphereHomeomorph_symm_apply_val (T : (CalderonN.X n) ≃ₗᵢ[ℝ] (CalderonN.X n)) (u : (UnitSphere n)) :
    ((orthogonalSphereHomeomorph T).symm u).val = T.symm u.val := rfl

theorem orthogonal_unitCone_preimage (T : (CalderonN.X n) ≃ₗᵢ[ℝ] (CalderonN.X n)) (s : Set (UnitSphere n)) :
    T ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' (orthogonalSphereHomeomorph T ⁻¹' s)) := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨r,hr,w,⟨u,hu,huw⟩,he⟩
    subst w
    refine ⟨r,hr,T.symm u.val,?_,?_⟩
    · refine ⟨(orthogonalSphereHomeomorph T).symm u,?_,rfl⟩
      simpa only [mem_preimage,(orthogonalSphereHomeomorph T).apply_symm_apply] using hu
    · have h := congrArg T.symm he
      simpa only [T.symm.map_smul,T.symm_apply_apply] using h
  · intro hv
    rcases hv with ⟨r,hr,w,⟨u,hu,huw⟩,he⟩
    subst w
    refine ⟨r,hr,T u.val,⟨orthogonalSphereHomeomorph T u,hu,rfl⟩,?_⟩
    have h := congrArg T he
    simpa only [T.map_smul] using h

theorem orthogonalSphereHomeomorph_surfaceMeasure_preserving (T : (CalderonN.X n) ≃ₗᵢ[ℝ] (CalderonN.X n)) :
    MeasurePreserving (orthogonalSphereHomeomorph T) ((volume : Measure (CalderonN.X n)).toSphere) ((volume : Measure (CalderonN.X n)).toSphere) := by
  refine ⟨(orthogonalSphereHomeomorph T).measurable,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (orthogonalSphereHomeomorph T).measurable hs]
  change (volume : Measure (CalderonN.X n)).toSphere (orthogonalSphereHomeomorph T ⁻¹' s) =
    (volume : Measure (CalderonN.X n)).toSphere s
  rw [Measure.toSphere_apply' _ ((orthogonalSphereHomeomorph T).measurable hs),
    Measure.toSphere_apply' _ hs,← orthogonal_unitCone_preimage T s]
  rw [T.measurePreserving.measure_preimage_emb T.toHomeomorph.measurableEmbedding]

theorem orthogonalSphereHomeomorph_sphereProbability_preserving (T : (CalderonN.X n) ≃ₗᵢ[ℝ] (CalderonN.X n)) :
    MeasurePreserving (orthogonalSphereHomeomorph T) (unitSphereProbability n) (unitSphereProbability n) := by
  refine ⟨(orthogonalSphereHomeomorph T).measurable,?_⟩
  let μ : Measure (UnitSphere n) := (volume : Measure (X n)).toSphere
  change Measure.map (orthogonalSphereHomeomorph T) ((μ univ)⁻¹ • μ) = (μ univ)⁻¹ • μ
  rw [Measure.map_smul,
    (orthogonalSphereHomeomorph_surfaceMeasure_preserving T).map_eq]
  exact (orthogonalSphereHomeomorph T).measurable.aemeasurable

end OAI.AnisotropicCalderon.OrthogonalSphereMeasure
