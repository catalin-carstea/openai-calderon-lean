module

public import Proof.CalderonN.HarmonicDerivativeBounds
public import Proof.CalderonN.SmoothHarmonicWeights

import Mathlib.Tactic

public section

/- The normalized angular shifts of the checked Proposition 5.3 proof,
   using its adjoint identity and the general-dimensional Hilbert sum. -/
noncomputable section
open scoped InnerProductSpace ENNReal

namespace CalderonN

open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

private abbrev HarmonicSequence (n : ℕ) [NeZero n] :=
  lp (fun k : ℕ => harmonicSphereSubspace n k) 2

private theorem lowerSequence_bound
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C)
    (u : HarmonicSequence n) (s : Finset ℕ) :
    (∑ k ∈ s, ‖A k (u (k+1))‖^2) ≤ (C * ‖u‖)^2 := by
  let f : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  have hsum := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u (s.map f)
  push_cast at hsum
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Finset.sum_map] at hsum
  change (∑ k ∈ s, ‖u (k+1)‖^2) ≤ ‖u‖^2 at hsum
  calc
    _ ≤ ∑ k ∈ s, C^2 * ‖u (k+1)‖^2 := Finset.sum_le_sum fun k _ => by
      rw [← mul_pow]
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr
        ((A k).le_of_opNorm_le (hA k) (u (k+1)))
    _ = C^2 * (∑ k ∈ s, ‖u (k+1)‖^2) := (Finset.mul_sum ..).symm
    _ ≤ (C * ‖u‖)^2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hsum (sq_nonneg C)

private def lowerSequence
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C) (u : HarmonicSequence n) :
    HarmonicSequence n := by
  refine ⟨(fun k => A k (u (k+1))), memℓp_gen' (C := (C * ‖u‖)^2) ?_⟩
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lowerSequence_bound A hC hA u

private def lowerHarmonics
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C) : SphereL2 n →L[ℝ] SphereL2 n := by
  let e := sphereHarmonicDecomposition (n := n)
  let L : HarmonicSequence n →ₗ[ℝ] HarmonicSequence n := {
    toFun := lowerSequence A hC hA
    map_add' := by
      intro u v
      apply lp.ext
      funext k
      exact (A k).map_add (u (k+1)) (v (k+1))
    map_smul' := by
      intro c u
      apply lp.ext
      funext k
      exact (A k).map_smul c (u (k+1)) }
  let G := e.symm.toLinearEquiv.toLinearMap.comp (L.comp e.toLinearEquiv.toLinearMap)
  refine G.mkContinuous C (fun u => ?_)
  change ‖e.symm (lowerSequence A hC hA (e u))‖ ≤ C * ‖u‖
  rw [LinearIsometryEquiv.norm_map, ← e.norm_map u]
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (by positivity)
  intro s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  change (∑ k ∈ s, ‖A k (e u (k+1))‖^2) ≤ (C * ‖e u‖)^2
  exact lowerSequence_bound A hC hA (e u) s

private theorem lowerHarmonics_projection
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C) (u : SphereL2 n) (k : ℕ) :
    harmonicProjection k (lowerHarmonics A hC hA u) = A k (harmonicProjection (k+1) u) := by
  rw [← sphereHarmonicDecomposition_apply, ← sphereHarmonicDecomposition_apply]
  change (sphereHarmonicDecomposition
    (sphereHarmonicDecomposition.symm (lowerSequence A hC hA (sphereHarmonicDecomposition u)))) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

private theorem lowerHarmonics_of_harmonic_succ
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C)
    {k : ℕ} (v : harmonicSphereSubspace n (k+1)) :
    lowerHarmonics A hC hA (v : SphereL2 n) = (A k v : SphereL2 n) := by
  apply sphereHarmonicDecomposition.injective
  rw [sphereHarmonicDecomposition_subtype]
  apply lp.ext
  funext j
  change (sphereHarmonicDecomposition (lowerHarmonics A hC hA (v : SphereL2 n))) j = _
  rw [sphereHarmonicDecomposition_apply, lowerHarmonics_projection,
    ← sphereHarmonicDecomposition_apply, sphereHarmonicDecomposition_subtype]
  by_cases hj : j = k
  · subst j
    simp only [lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ (fun e => hj (Nat.succ_injective e)),
      lp.single_apply_ne _ _ _ hj, map_zero]

private theorem lowerHarmonics_of_harmonic_zero
    (A : ∀ k : ℕ, harmonicSphereSubspace n (k+1) →L[ℝ] harmonicSphereSubspace n k)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ k, ‖A k‖ ≤ C)
    (v : harmonicSphereSubspace n 0) :
    lowerHarmonics A hC hA (v : SphereL2 n) = 0 := by
  apply sphereHarmonicDecomposition.injective
  rw [map_zero]
  apply lp.ext
  funext j
  change (sphereHarmonicDecomposition (lowerHarmonics A hC hA (v : SphereL2 n))) j = 0
  rw [sphereHarmonicDecomposition_apply, lowerHarmonics_projection,
    ← sphereHarmonicDecomposition_apply, sphereHarmonicDecomposition_subtype,
    lp.single_apply_ne _ _ _ (by omega), map_zero]

private theorem norm_scaled_harmonicDerivative_le (m : ℕ) (i : I n)
    (q : ℝ) (hq : (m : ℝ) + 1 ≤ q) :
    ‖q⁻¹ • harmonicDerivative (sphereFischerInner n) m i‖ ≤ (n : ℝ) + 2 := by
  have hq₀ : 0 < q := lt_of_lt_of_le (by positivity) hq
  calc
    _ ≤ q⁻¹ * ‖harmonicDerivative (sphereFischerInner n) m i‖ := by
      simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hq₀)] using
        ContinuousLinearMap.opNorm_smul_le (q⁻¹) (harmonicDerivative (sphereFischerInner n) m i)
    _ ≤ q⁻¹ * (((n : ℝ)+2) * ((m:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left (norm_harmonicDerivative_le (sphereFischerInner n) m i)
        (inv_nonneg.mpr hq₀.le)
    _ ≤ q⁻¹ * (((n : ℝ)+2) * q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by positivity))
        (inv_nonneg.mpr hq₀.le)
    _ = _ := by rw [← mul_assoc, mul_comm (q⁻¹) _, mul_assoc, inv_mul_cancel₀ hq₀.ne', mul_one]

/-- Lowering after undoing one Bessel weight in the input degree. -/
def normalizedLowering (i : I n) : SphereL2 n →L[ℝ] SphereL2 n :=
  lowerHarmonics (fun k => ((k : ℝ)+2)⁻¹ • harmonicDerivative (sphereFischerInner n) k i)
    (C := (n : ℝ)+2) (by positivity)
    (fun k => norm_scaled_harmonicDerivative_le k i _ (by linarith))

theorem normalizedLowering_projection (i : I n) (k : ℕ) (u : SphereL2 n) :
    harmonicProjection k (normalizedLowering i u) =
      ((k : ℝ)+2)⁻¹ • harmonicDerivative (sphereFischerInner n) k i (harmonicProjection (k+1) u) :=
  lowerHarmonics_projection _ _ _ u k

/-- Raising after undoing one Bessel weight in the input degree. -/
def normalizedRaising (i : I n) : SphereL2 n →L[ℝ] SphereL2 n :=
  ContinuousLinearMap.adjoint
    (lowerHarmonics (fun k => ((k : ℝ)+1)⁻¹ • harmonicDerivative (sphereFischerInner n) k i)
      (C := (n : ℝ)+2) (by positivity)
      (fun k => norm_scaled_harmonicDerivative_le k i _ le_rfl))

theorem normalizedRaising_projection_zero (i : I n) (u : SphereL2 n) :
    harmonicProjection 0 (normalizedRaising i u) = 0 := by
  apply ext_inner_right ℝ
  intro v
  rw [harmonicProjection_inner, inner_zero_left, normalizedRaising,
    ContinuousLinearMap.adjoint_inner_left, lowerHarmonics_of_harmonic_zero, inner_zero_right]

theorem normalizedRaising_projection_succ (i : I n) (k : ℕ) (u : SphereL2 n) :
    harmonicProjection (k+1) (normalizedRaising i u) =
      ((k : ℝ)+1)⁻¹ • harmonicDerivativeAdjoint (sphereFischerInner n) k i (harmonicProjection k u) := by
  apply ext_inner_right ℝ
  intro v
  rw [harmonicProjection_inner, normalizedRaising, ContinuousLinearMap.adjoint_inner_left,
    lowerHarmonics_of_harmonic_succ]
  calc
    _ = ((k : ℝ)+1)⁻¹ * ⟪u, (harmonicDerivative (sphereFischerInner n) k i v : SphereL2 n)⟫_ℝ := by
      simp only [ContinuousLinearMap.smul_apply, Submodule.coe_smul, real_inner_smul_right]
    _ = _ := by
      change _ = ⟪((((k:ℝ)+1)⁻¹ •
        harmonicDerivativeAdjoint (sphereFischerInner n) k i (harmonicProjection k u) :
          harmonicSphereSubspace n (k+1)) : SphereL2 n), (v : SphereL2 n)⟫_ℝ
      rw [Submodule.coe_smul, real_inner_smul_left]
      congr 1
      rw [← harmonicProjection_inner k u (harmonicDerivative (sphereFischerInner n) k i v)]
      exact (inner_harmonicDerivativeAdjoint (sphereFischerInner n) k i (harmonicProjection k u) v).symm

end CalderonN
