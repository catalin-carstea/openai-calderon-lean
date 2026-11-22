module

public import Proof.CalderonN.SmoothHarmonicWeights
public import Proof.CalderonN.HarmonicHilbertDecomposition

import Mathlib.Tactic

/-! Adapted from the released Proposition 5.3 `SphereSobolevCompletion`.
The same orthogonal degree spaces now use the ambient dimension. -/

public section

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology ENNReal InnerProductSpace

namespace CalderonN

open OAI.AnisotropicCalderon.SphereHarmonic

abbrev SphereSobolev (dim : ℕ) [NeZero dim] (_s : ℝ) :=
  lp (fun k : ℕ => harmonicSphereSubspace dim k) 2

variable {dim : ℕ} [NeZero dim]

theorem besselWeight_pos (s : ℝ) (k : ℕ) : 0 < besselWeight s k :=
  Real.rpow_pos_of_pos (by positivity) _

def sphereSobolevCoefficientL (s : ℝ) (k : ℕ) :
    SphereSobolev dim s →L[ℝ] harmonicSphereSubspace dim k :=
  (besselWeight (-s) k) • (lp.evalCLM ℝ (fun j : ℕ => harmonicSphereSubspace dim j) 2 k)

theorem sphereSobolevCoefficientL_apply (s : ℝ) (k : ℕ) (u : SphereSobolev dim s) :
    sphereSobolevCoefficientL s k u = besselWeight (-s) k • u k := by
  unfold sphereSobolevCoefficientL
  rfl

theorem sphereSobolevCoefficientL_reconstruct (s : ℝ) (k : ℕ)
    (u : SphereSobolev dim s) :
    besselWeight s k • sphereSobolevCoefficientL s k u = u k := by
  change besselWeight s k • (besselWeight (-s) k • u k) = u k
  rw [smul_smul]
  have hw : besselWeight s k * besselWeight (-s) k = 1 := by
    simpa only [besselWeight, add_neg_cancel, Real.rpow_zero] using
      (Real.rpow_add (by positivity : 0 < 1 + (k : ℝ)) s (-s)).symm
  rw [hw, one_smul]

theorem sphereSobolev_ext (s : ℝ) (u v : SphereSobolev dim s)
    (h : ∀ k : ℕ, sphereSobolevCoefficientL s k u = sphereSobolevCoefficientL s k v) :
    u = v := by
  apply lp.ext
  funext k
  rw [← sphereSobolevCoefficientL_reconstruct s k u,
    ← sphereSobolevCoefficientL_reconstruct s k v, h k]

theorem norm_sq_sphereSobolev (s : ℝ) (u : SphereSobolev dim s) :
    ‖u‖ ^ 2 = ∑' k : ℕ, besselWeight s k ^ 2 *
      ‖sphereSobolevCoefficientL s k u‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (show 0 < (2 : ℝ≥0∞).toReal by norm_num) u
  have h2 : ‖u‖ ^ 2 = ∑' k : ℕ, ‖u k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  rw [h2]
  apply tsum_congr
  intro k
  rw [← sphereSobolevCoefficientL_reconstruct s k u, norm_smul,
    Real.norm_eq_abs, abs_of_pos (besselWeight_pos s k), mul_pow]

@[expose] def sphereSobolevSingleL (s : ℝ) (k : ℕ) :
    harmonicSphereSubspace dim k →L[ℝ] SphereSobolev dim s :=
  (besselWeight s k) • (lp.singleContinuousLinearMap ℝ
    (fun j : ℕ => harmonicSphereSubspace dim j) 2 k)

theorem sphereSobolevCoefficientL_single_self (s : ℝ) (k : ℕ)
    (a : harmonicSphereSubspace dim k) :
    sphereSobolevCoefficientL s k (sphereSobolevSingleL s k a) = a := by
  change besselWeight (-s) k • (besselWeight s k • (lp.single (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 k a) k) = a
  rw [lp.single_apply_self, smul_smul]
  have hw : besselWeight (-s) k * besselWeight s k = 1 := by
    simpa only [besselWeight, neg_add_cancel, Real.rpow_zero] using
      (Real.rpow_add (by positivity : 0 < 1 + (k : ℝ)) (-s) s).symm
  rw [hw, one_smul]

theorem sphereSobolevCoefficientL_single_ne (s : ℝ) (j k : ℕ)
    (hkj : k ≠ j) (a : harmonicSphereSubspace dim j) :
    sphereSobolevCoefficientL s k (sphereSobolevSingleL s j a) = 0 := by
  change besselWeight (-s) k • (besselWeight s j • (lp.single (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 j a) k) = 0
  rw [lp.single_apply_ne (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 j a hkj, smul_zero, smul_zero]

theorem norm_sphereSobolevSingleL_apply (s : ℝ) (k : ℕ)
    (a : harmonicSphereSubspace dim k) :
    ‖sphereSobolevSingleL s k a‖ = besselWeight s k * ‖a‖ := by
  change ‖besselWeight s k • lp.single (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 k a‖ = besselWeight s k * ‖a‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (besselWeight_pos s k),
    lp.norm_single (E := fun j : ℕ => harmonicSphereSubspace dim j) (show 0 < (2 : ℝ≥0∞) by norm_num)]

@[expose] def sphereSobolevPartialSum (s : ℝ) (n : ℕ) (u : SphereSobolev dim s) :
    SphereSobolev dim s :=
  ∑ k ∈ Finset.range n, sphereSobolevSingleL s k (sphereSobolevCoefficientL s k u)

theorem sphereSobolevPartialSum_eq (s : ℝ) (n : ℕ) (u : SphereSobolev dim s) :
    sphereSobolevPartialSum s n u = ∑ k ∈ Finset.range n, lp.single 2 k (u k) := by
  unfold sphereSobolevPartialSum
  apply Finset.sum_congr rfl
  intro k hk
  change besselWeight s k • lp.single (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 k (sphereSobolevCoefficientL s k u) =
    lp.single (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 k (u k)
  rw [← lp.single_smul, sphereSobolevCoefficientL_reconstruct]

theorem sphereSobolevCoefficientL_partialSum (s : ℝ) (n k : ℕ)
    (u : SphereSobolev dim s) :
    sphereSobolevCoefficientL s k (sphereSobolevPartialSum s n u) =
      if k < n then sphereSobolevCoefficientL s k u else 0 := by
  rw [sphereSobolevPartialSum_eq]
  change besselWeight (-s) k • (∑ j ∈ Finset.range n, lp.single (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 j (u j)) k =
    if k < n then besselWeight (-s) k • u k else 0
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single]
  by_cases hk : k < n
  · simp only [Finset.mem_range, hk, ite_true]
  · simp only [Finset.mem_range, hk, ite_false, smul_zero]

@[expose] def sphereSobolevFiniteSupport (s : ℝ) : Set (SphereSobolev dim s) :=
  {u | ∃ n : ℕ, ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL s k u = 0}

theorem sphereSobolevPartialSum_mem_finiteSupport (s : ℝ) (n : ℕ)
    (u : SphereSobolev dim s) :
    sphereSobolevPartialSum s n u ∈ sphereSobolevFiniteSupport s := by
  refine ⟨n, ?_⟩
  intro k hk
  rw [sphereSobolevCoefficientL_partialSum, ite_eq_right (fun h => absurd h (not_lt.mpr hk))]

theorem tendsto_sphereSobolevPartialSum (s : ℝ) (u : SphereSobolev dim s) :
    Tendsto (fun n : ℕ => sphereSobolevPartialSum s n u) atTop (𝓝 u) := by
  simpa only [sphereSobolevPartialSum_eq] using
    (lp.hasSum_single (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num) u).tendsto_sum_nat

theorem closure_sphereSobolevFiniteSupport (s : ℝ) :
    closure (sphereSobolevFiniteSupport (dim := dim) s) = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ _) ?_
  intro u hu
  exact isClosed_closure.mem_of_tendsto (tendsto_sphereSobolevPartialSum s u)
    (Eventually.of_forall fun n =>
      subset_closure (sphereSobolevPartialSum_mem_finiteSupport s n u))

def sphereSobolevBesselEquiv (s t : ℝ) :
    SphereSobolev dim s ≃ₗᵢ[ℝ] SphereSobolev dim (s - t) :=
  LinearIsometryEquiv.refl ℝ (SphereSobolev dim s)

theorem sphereSobolevCoefficientL_besselEquiv (s t : ℝ) (k : ℕ)
    (u : SphereSobolev dim s) :
    sphereSobolevCoefficientL (s - t) k (sphereSobolevBesselEquiv s t u) =
      besselWeight t k • sphereSobolevCoefficientL s k u := by
  change besselWeight (-(s - t)) k • u k =
    besselWeight t k • (besselWeight (-s) k • u k)
  rw [smul_smul]
  have he : -(s - t) = t + (-s) := by ring
  unfold besselWeight
  rw [he, Real.rpow_add (by positivity : 0 < 1 + (k : ℝ))]

def sphereSobolevZeroEquiv : SphereL2 dim ≃ₗᵢ[ℝ] SphereSobolev dim 0 :=
  sphereHarmonicDecomposition

theorem sphereSobolevCoefficientL_zeroEquiv (k : ℕ) (u : SphereL2 dim) :
    sphereSobolevCoefficientL 0 k (sphereSobolevZeroEquiv u) = harmonicProjection k u := by
  change besselWeight (-0) k • sphereHarmonicDecomposition u k = _
  rw [sphereHarmonicDecomposition_apply]
  simp [besselWeight]

end CalderonN
