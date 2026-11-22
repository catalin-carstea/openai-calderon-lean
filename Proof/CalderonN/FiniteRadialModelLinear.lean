module

public import Proof.CalderonN.PolynomialConormalFirstVariation
public import Proof.CalderonN.BallRadialDerivative
public import Proof.CalderonN.PolynomialBallSobolev

import Mathlib.Tactic

/-! The flat solid harmonics and their polynomial drift correction as
linear maps on the common finite coefficient space. -/

public section

noncomputable section
open MvPolynomial
open scoped ContDiff Classical DirectSum
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace

variable {dim : ℕ} [NeZero dim]

@[expose] def harmonicFiniteSmoothL : HarmonicFiniteCoefficients dim →ₗ[ℝ] smoothBallDataSubmodule dim :=
  (polynomialSmoothDataL (dim := dim)).comp
    (DirectSum.toModule ℝ ℕ _ harmonicPolynomialRepresentativeL)

theorem harmonicFiniteSmoothL_val (f : HarmonicFiniteCoefficients dim) :
    (harmonicFiniteSmoothL f).1 = (harmonicFiniteSmooth f).1 := by
  have h : DirectSum.toModule ℝ ℕ (MvPolynomial (Fin dim) ℝ) harmonicPolynomialRepresentativeL f =
      harmonicFinitePolynomial f := by
    conv_lhs => rw [← DirectSum.sum_support_of f,map_sum]
    unfold harmonicFinitePolynomial
    apply Finset.sum_congr rfl
    intro k _
    exact DirectSum.toModule_lof (R := ℝ) (φ := harmonicPolynomialRepresentativeL) k (f k)
  unfold harmonicFiniteSmoothL harmonicFiniteSmooth
  rw [LinearMap.comp_apply,h]
  rfl

theorem harmonicFiniteSmoothL_lof (k : ℕ) (v : harmonicSphereSubspace dim k) :
    (harmonicFiniteSmoothL (DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k v)).1 =
      polynomialEvaluation (harmonicPolynomialRepresentativeL k v) := by
  rw [harmonicFiniteSmoothL,LinearMap.comp_apply,DirectSum.toModule_lof]
  rfl

private def driftDerivativeL (b : Fin dim → ℝ) :
    MvPolynomial (Fin dim) ℝ →ₗ[ℝ] MvPolynomial (Fin dim) ℝ :=
  ∑ i, (LinearMap.mulLeft ℝ (C (b i))).comp ((pderiv i).toLinearMap)

private theorem driftDerivativeL_apply (b : Fin dim → ℝ) (p : MvPolynomial (Fin dim) ℝ) :
    driftDerivativeL b p = driftDerivative b p := by
  unfold driftDerivativeL driftDerivative
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,Derivation.coeFn_coe]

private def driftFirstVariationL (k : ℕ) (b : Fin dim → ℝ) :
    MvPolynomial (Fin dim) ℝ →ₗ[ℝ] MvPolynomial (Fin dim) ℝ :=
  ((LinearMap.mulLeft ℝ (C (-(4*(((k-1 : ℕ) : ℝ))+2*(Fintype.card (Fin dim) : ℝ))⁻¹))).comp
    (LinearMap.mulLeft ℝ (radiusSq-1))).comp (driftDerivativeL b)

private theorem driftFirstVariationL_apply (k : ℕ) (b : Fin dim → ℝ) (p : MvPolynomial (Fin dim) ℝ) :
    driftFirstVariationL k b p = driftFirstVariation k b p := by
  unfold driftFirstVariationL driftFirstVariation radialFirstVariation
  simp only [LinearMap.comp_apply,LinearMap.mulLeft_apply,driftDerivativeL_apply]

def harmonicFiniteDriftVariationSmoothL (ell : X dim →L[ℝ] ℝ) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] smoothBallDataSubmodule dim :=
  (polynomialSmoothDataL (dim := dim)).comp (DirectSum.toModule ℝ ℕ _
    (fun k => (driftFirstVariationL k fun i => ell (axis i)).comp (harmonicPolynomialRepresentativeL k)))

theorem harmonicFiniteDriftVariationSmoothL_val (ell : X dim →L[ℝ] ℝ)
    (f : HarmonicFiniteCoefficients dim) :
    (harmonicFiniteDriftVariationSmoothL ell f).1 = (harmonicFiniteDriftVariationSmooth ell f).1 := by
  let L (k : ℕ) := (driftFirstVariationL k fun i => ell (axis i)).comp (harmonicPolynomialRepresentativeL k)
  have h : DirectSum.toModule ℝ ℕ (MvPolynomial (Fin dim) ℝ) L f =
      ∑ k ∈ f.support, driftFirstVariation k (fun i => ell (axis i)) (harmonicPolynomialRepresentativeL k (f k)) := by
    conv_lhs => rw [← DirectSum.sum_support_of f,map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact (DirectSum.toModule_lof (R := ℝ) (φ := L) k (f k)).trans
      (driftFirstVariationL_apply k (fun i => ell (axis i)) (harmonicPolynomialRepresentativeL k (f k)))
  unfold harmonicFiniteDriftVariationSmoothL harmonicFiniteDriftVariationSmooth
  rw [LinearMap.comp_apply,show (fun k =>
    (driftFirstVariationL k fun i => ell (axis i)).comp (harmonicPolynomialRepresentativeL k)) = L from rfl,h]
  rfl

theorem harmonicFiniteDriftVariationSmoothL_lof (ell : X dim →L[ℝ] ℝ)
    (k : ℕ) (v : harmonicSphereSubspace dim k) :
    (harmonicFiniteDriftVariationSmoothL ell
      (DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k v)).1 =
      polynomialEvaluation (driftFirstVariation k (fun i => ell (axis i))
        (harmonicPolynomialRepresentativeL k v)) := by
  rw [harmonicFiniteDriftVariationSmoothL,LinearMap.comp_apply,DirectSum.toModule_lof,
    LinearMap.comp_apply,driftFirstVariationL_apply]
  rfl

@[expose] def smoothBallRadialDataL : smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim where
  toFun u := ⟨(smoothBallRadialDerivative ⟨u.1,smoothBallData_contDiff u⟩).1,
    (smoothBallRadialDerivative ⟨u.1,smoothBallData_contDiff u⟩).2⟩
  map_add' u v := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (fun x => u.1 x+v.1 x) z z = fderiv ℝ u.1 z z+fderiv ℝ v.1 z z
    rw [fderiv_fun_add ((smoothBallData_contDiff u).differentiable (by simp) z)
      ((smoothBallData_contDiff v).differentiable (by simp) z),add_apply]
  map_smul' c u := by
    apply Subtype.ext
    funext z
    change fderiv ℝ (c • u.1) z z = c*fderiv ℝ u.1 z z
    rw [fderiv_const_smul ((smoothBallData_contDiff u).differentiable (by simp) z),
      smul_apply,smul_eq_mul]

theorem smoothBallRadialDataL_val (u : smoothBallDataSubmodule dim) :
    (smoothBallRadialDataL u).1 = fun z => fderiv ℝ u.1 z z := by
  unfold smoothBallRadialDataL
  rfl

end CalderonN
