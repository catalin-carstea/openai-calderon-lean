module

public import Proof.CalderonN.WeightedHarmonicConvergence

import Mathlib.Tactic

public section

/- The bounded spectral multiplier from Proposition 5.3 release f308cb9d,
   constructed using the shared Hilbert sum of the actual spherical harmonics. -/
noncomputable section
open scoped ENNReal

namespace CalderonN

open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

private abbrev HarmonicSequence (n : ℕ) [NeZero n] :=
  lp (fun k : ℕ => harmonicSphereSubspace n k) 2

private def weightSequence (w : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C)
    (u : HarmonicSequence n) : HarmonicSequence n := by
  refine ⟨fun k => w k • u k, (lp.memℓp (C • u)).mono' (fun k => ?_)⟩
  change ‖w k • u k‖ ≤ ‖C • u k‖
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using
    mul_le_mul_of_nonneg_right (hw k) (norm_nonneg (u k))

/-- Bounded real weights act diagonally on the harmonic decomposition. -/
def harmonicMultiplier (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ k, |w k| ≤ C) :
    SphereL2 n →L[ℝ] SphereL2 n := by
  let e := sphereHarmonicDecomposition (n := n)
  let L : HarmonicSequence n →ₗ[ℝ] HarmonicSequence n := {
    toFun := weightSequence w hC hw
    map_add' := by
      intro u v
      apply lp.ext
      funext k
      change w k • (u k + v k) = w k • u k + w k • v k
      exact smul_add _ _ _
    map_smul' := by
      intro c u
      apply lp.ext
      funext k
      change w k • (c • u k) = c • (w k • u k)
      exact smul_comm _ _ _ }
  let A := e.symm.toLinearEquiv.toLinearMap.comp (L.comp e.toLinearEquiv.toLinearMap)
  refine A.mkContinuous C (fun u => ?_)
  change ‖e.symm (weightSequence w hC hw (e u))‖ ≤ C * ‖u‖
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖C • e u‖ := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (fun k => by
      change ‖w k • e u k‖ ≤ ‖C • e u k‖
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] using
        mul_le_mul_of_nonneg_right (hw k) (norm_nonneg (e u k)))
    _ = C * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, e.norm_map]

theorem harmonicProjection_harmonicMultiplier (w : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ k, |w k| ≤ C) (u : SphereL2 n) (k : ℕ) :
    harmonicProjection k (harmonicMultiplier w C hC hw u) = w k • harmonicProjection k u := by
  rw [← sphereHarmonicDecomposition_apply, ← sphereHarmonicDecomposition_apply]
  change (sphereHarmonicDecomposition
    (sphereHarmonicDecomposition.symm (weightSequence w hC hw (sphereHarmonicDecomposition u)))) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

end CalderonN
