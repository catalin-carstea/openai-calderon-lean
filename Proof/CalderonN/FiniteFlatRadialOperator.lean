module

public import Proof.CalderonN.FiniteRadialModelLinear
public import Proof.CalderonN.FiniteHarmonicPackets
public import Proof.CalderonN.SmoothBoundaryHilbert
public import Proof.CalderonN.FiniteSphereMidpoint

import Mathlib.Tactic

/-! The flat radial trace is the degree multiplier on the common
finite solid-harmonic lift. -/

public section

noncomputable section
open Set MvPolynomial
open scoped ContDiff DirectSum InnerProductSpace Classical
set_option autoImplicit false
set_option maxHeartbeats 2700000
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim]

@[expose] def finiteHarmonicDegreeL : HarmonicFiniteCoefficients dim →ₗ[ℝ] HarmonicFiniteCoefficients dim :=
  DirectSum.lmap (fun k => (k:ℝ) • (LinearMap.id :
    harmonicSphereSubspace dim k →ₗ[ℝ] harmonicSphereSubspace dim k))

theorem finiteHarmonicDegreeL_lof (k : ℕ) (u : harmonicSphereSubspace dim k) :
    finiteHarmonicDegreeL (DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k u) =
      DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k ((k:ℝ) • u) := by
  rw [finiteHarmonicDegreeL,DirectSum.lmap_lof]
  rfl

theorem finiteHarmonicDegreeL_packet (s : Finset ℕ) (v : ∀ k, harmonicSphereSubspace dim k) :
    finiteHarmonicDegreeL (finiteHarmonicPacket s v) =
      finiteHarmonicPacket s (fun k => (k:ℝ) • v k) := by
  simp only [finiteHarmonicPacket,map_sum,finiteHarmonicDegreeL_lof]

theorem harmonicFiniteSmooth_degree_eq_radial (f : HarmonicFiniteCoefficients dim) :
    (harmonicFiniteSmooth (finiteHarmonicDegreeL f)).1 = fun z =>
      fderiv ℝ (harmonicFiniteSmooth f).1 z z := by
  have h : harmonicFiniteSmoothL.comp (finiteHarmonicDegreeL (dim:=dim)) =
      smoothBallRadialDataL.comp harmonicFiniteSmoothL := by
    ext k u : 2
    simp only [LinearMap.comp_apply,finiteHarmonicDegreeL_lof]
    apply Subtype.ext
    rw [smoothBallRadialDataL_val,harmonicFiniteSmoothL_lof,harmonicFiniteSmoothL_lof]
    funext z
    rw [radialDerivative_homogeneous_polynomialEvaluation k _ (harmonicPolynomialRepresentative_mem k u).1,
      map_smul]
    unfold OAI.AnisotropicCalderon.GreenRadialTrace.polynomialEvaluation
    rw [smul_eq_C_mul,map_mul,eval_C]
  rw [← harmonicFiniteSmoothL_val,← harmonicFiniteSmoothL_val]
  exact congrArg (fun L : HarmonicFiniteCoefficients dim →ₗ[ℝ] smoothBallDataSubmodule dim => (L f).1) h

theorem norm_flat_finite_radial_zero_le (hn : 3 ≤ dim) (f : HarmonicFiniteCoefficients dim) :
    ‖smoothBoundarySobolev hn 0 (by norm_num)
      (smoothBallRadialDerivative (harmonicFiniteSmooth f))‖ ≤
      ‖harmonicBoundaryFiniteL 1 f‖ := by
  rw [smoothBoundarySobolev_eq_of_eqOn hn 0 (by norm_num) _ (harmonicFiniteSmooth (finiteHarmonicDegreeL f))
      (fun z _ => congrFun (harmonicFiniteSmooth_degree_eq_radial f).symm z),
    smoothBoundarySobolev_harmonicFiniteSmooth]
  rw [← finiteHarmonicPacket_support f,finiteHarmonicDegreeL_packet,norm_finiteHarmonicPacket,
    norm_finiteHarmonicPacket]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro k _
  simp only [besselWeight,Real.rpow_zero,Real.rpow_one,one_pow,one_mul,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) k),mul_pow]
  exact mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α:=ℝ) k]) (sq_nonneg _)

theorem norm_harmonicBoundaryFiniteL_zero_le_one (f : HarmonicFiniteCoefficients dim) :
    ‖harmonicBoundaryFiniteL 0 f‖ ≤ ‖harmonicBoundaryFiniteL 1 f‖ := by
  let J := sphereSobolevInclusionL (dim:=dim) 1 0 (by norm_num)
  have hJ := norm_sphereSobolevInclusionL_le (dim:=dim) 1 0 (by norm_num)
  rw [← sphereSobolevInclusionL_harmonicBoundaryFiniteL 1 0 (by norm_num)]
  exact (J.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hJ (norm_nonneg _))

end CalderonN
