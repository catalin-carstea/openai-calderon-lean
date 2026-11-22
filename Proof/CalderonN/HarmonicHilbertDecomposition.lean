module

public import Proof.CalderonN.DenseSphereHarmonics
public import Proof.CalderonN.ZonalProjection
public import Mathlib.Analysis.InnerProductSpace.l2Space

import Mathlib.Tactic.NormNum

public section

/- The Hilbert sum argument follows SphereHilbertDecomposition and
   LegendreHilbert from Proposition 5.3 check f308cb9d. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace CalderonN
open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

theorem isHilbertSum_harmonicSphereSubspaces :
    IsHilbertSum ℝ (fun k : ℕ => ↥(harmonicSphereSubspace n k))
      (fun k => (harmonicSphereSubspace n k).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal
  · intro i j hij u v
    exact orthogonalSphereHarmonics n i j hij u u.property v v.property
  · change ⊤ ≤ (⨆ k : ℕ, harmonicSphereSubspace n k).topologicalClosure
    rw [denseSphereHarmonics n]

def sphereHarmonicDecomposition :
    SphereL2 n ≃ₗᵢ[ℝ] lp (fun k : ℕ => harmonicSphereSubspace n k) 2 :=
  isHilbertSum_harmonicSphereSubspaces.linearIsometryEquiv

private theorem inner_sphereHarmonicDecomposition (u v : SphereL2 n) :
    ⟪u, v⟫_ℝ = ∑' k : ℕ,
      ⟪sphereHarmonicDecomposition u k, sphereHarmonicDecomposition v k⟫_ℝ := by
  rw [← sphereHarmonicDecomposition.inner_map_map u v]
  exact lp.inner_eq_tsum _ _

theorem sphereHarmonicDecomposition_subtype (k : ℕ) (v : harmonicSphereSubspace n k) :
    sphereHarmonicDecomposition (v : SphereL2 n) = lp.single 2 k v := by
  apply sphereHarmonicDecomposition.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (IsHilbertSum.linearIsometryEquiv_symm_apply_single
    isHilbertSum_harmonicSphereSubspaces v).symm

theorem sphereHarmonicDecomposition_apply (k : ℕ) (u : SphereL2 n) :
    sphereHarmonicDecomposition u k = harmonicProjection k u := by
  apply ext_inner_left ℝ
  intro v
  have hs := inner_sphereHarmonicDecomposition (v : SphereL2 n) u
  rw [sphereHarmonicDecomposition_subtype k v, tsum_eq_single k] at hs
  · rw [lp.single_apply_self] at hs
    have hp := (harmonicSphereSubspace n k).inner_orthogonalProjectionOnto_eq_of_mem_left v u
    exact hs.symm.trans hp.symm
  · intro j hj
    rw [lp.single_apply_ne (E := fun j => harmonicSphereSubspace n j) 2 k v hj,
      inner_zero_left]

theorem hasSum_harmonicProjection (u : SphereL2 n) :
    HasSum (fun k : ℕ => (harmonicProjection k u : SphereL2 n)) u := by
  have h := isHilbertSum_harmonicSphereSubspaces.hasSum_linearIsometryEquiv_symm
    (sphereHarmonicDecomposition u)
  have hcenter : isHilbertSum_harmonicSphereSubspaces.linearIsometryEquiv.symm
      (sphereHarmonicDecomposition u) = u := by
    rw [sphereHarmonicDecomposition, LinearIsometryEquiv.symm_apply_apply]
  rw [hcenter] at h
  simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype,
    sphereHarmonicDecomposition_apply] using h

/-- Parseval on the actual orthogonal degrees used by the zonal projector. -/
theorem norm_sq_harmonicProjection (u : SphereL2 n) :
    ‖u‖ ^ 2 = ∑' k : ℕ, ‖harmonicProjection k u‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    (sphereHarmonicDecomposition u)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    sphereHarmonicDecomposition_apply] using h

end CalderonN
