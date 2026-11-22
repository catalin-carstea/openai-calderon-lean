module

public import Proof.CalderonN.FiniteHarmonicRotation
public import Proof.CalderonN.HarmonicRotationCasimir

import Mathlib.Tactic

/-! Finite packets identify the block sums with the existing boundary
Sobolev norms without a choice of basis in each harmonic degree. -/

public section

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped DirectSum InnerProductSpace Classical
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim]

@[expose] def finiteHarmonicPacket (s : Finset ℕ) (u : ∀ k, harmonicSphereSubspace dim k) :
    HarmonicFiniteCoefficients dim :=
  ∑ k ∈ s, DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace dim k)) k (u k)

theorem harmonicBoundaryFiniteL_packet (σ : ℝ) (s : Finset ℕ)
    (u : ∀ k, harmonicSphereSubspace dim k) :
    harmonicBoundaryFiniteL σ (finiteHarmonicPacket s u) =
      ∑ k ∈ s, sphereSobolevSingleL σ k (u k) := by
  simp only [finiteHarmonicPacket,map_sum,harmonicBoundaryFiniteL,DirectSum.toModule_lof,
    ContinuousLinearMap.coe_coe]

theorem finiteHarmonicRotationL_packet (i j : Fin dim) (s : Finset ℕ)
    (u : ∀ k, harmonicSphereSubspace dim k) :
    finiteHarmonicRotationL i j (finiteHarmonicPacket s u) =
      finiteHarmonicPacket s (fun k => harmonicSphereRotation k i j (u k)) := by
  simp only [finiteHarmonicPacket,map_sum,finiteHarmonicRotationL_lof]

theorem finiteHarmonicPacket_support (f : HarmonicFiniteCoefficients dim) :
    finiteHarmonicPacket f.support f = f := DirectSum.sum_support_of f

theorem norm_finiteHarmonicPacket (σ : ℝ) (s : Finset ℕ)
    (u : ∀ k, harmonicSphereSubspace dim k) :
    ‖harmonicBoundaryFiniteL σ (finiteHarmonicPacket s u)‖ =
      Real.sqrt (∑ k ∈ s, besselWeight σ k^2*‖u k‖^2) := by
  rw [← norm_sq_finite_boundary_sum σ s u,Real.sqrt_sq (norm_nonneg _),
    harmonicBoundaryFiniteL_packet]

theorem sphereSobolevZeroEquiv_harmonic (k : ℕ) (v : harmonicSphereSubspace dim k) :
    sphereSobolevZeroEquiv (v : SphereL2 dim) = sphereSobolevSingleL 0 k v := by
  apply lp.ext
  funext j
  rw [← sphereSobolevCoefficientL_reconstruct 0 j (sphereSobolevZeroEquiv (v : SphereL2 dim)),
    sphereSobolevCoefficientL_zeroEquiv,← sphereHarmonicDecomposition_apply,
    sphereHarmonicDecomposition_subtype,sphereSobolevSingleL]
  simp [besselWeight]

theorem sphereSobolevZeroEquiv_symm_packet (s : Finset ℕ) (u : ∀ k, harmonicSphereSubspace dim k) :
    (sphereSobolevZeroEquiv (dim:=dim)).symm (harmonicBoundaryFiniteL 0 (finiteHarmonicPacket s u)) =
      ∑ k ∈ s, (u k : SphereL2 dim) := by
  apply (sphereSobolevZeroEquiv (dim:=dim)).injective
  simp only [LinearIsometryEquiv.apply_symm_apply,harmonicBoundaryFiniteL_packet,map_sum,
    sphereSobolevZeroEquiv_harmonic]

theorem norm_finiteHarmonicPacket_L2 (s : Finset ℕ) (u : ∀ k, harmonicSphereSubspace dim k) :
    ‖∑ k ∈ s, (u k : SphereL2 dim)‖ =
      ‖harmonicBoundaryFiniteL 0 (finiteHarmonicPacket s u)‖ := by
  rw [← sphereSobolevZeroEquiv_symm_packet,LinearIsometryEquiv.norm_map]

theorem norm_finiteRotation_L2_le (hn : 3 ≤ dim) (i j : Fin dim) (s : Finset ℕ)
    (u : ∀ k, harmonicSphereSubspace dim k) :
    ‖∑ k ∈ s, (harmonicSphereRotation k i j (u k) : SphereL2 dim)‖ ≤
      (2*(dim:ℝ))*‖harmonicBoundaryFiniteL 1 (finiteHarmonicPacket s u)‖ := by
  have hC : 0 ≤ (2*(dim:ℝ)) := by positivity
  rw [norm_finiteHarmonicPacket_L2,norm_finiteHarmonicPacket,norm_finiteHarmonicPacket]
  conv_rhs => rw [← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg (2*(dim:ℝ)))]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  simp only [besselWeight,Real.rpow_zero,one_pow,one_mul,Real.rpow_one]
  calc
    _ ≤ ((2*(dim:ℝ))*(1+(k:ℝ))*‖u k‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_harmonicSphereRotation_le hn k i j (u k)) 2
    _ = _ := by ring

end CalderonN
