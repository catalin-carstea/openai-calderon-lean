module

public import Proof.CalderonN.FiniteRadialModelLinear
public import Proof.CalderonN.SmoothSphereRotationProjection

import Mathlib.Tactic

/-! A solid rotation preserves the common finite boundary coefficient
space and commutes with its flat harmonic extension. -/

public section

noncomputable section
open MvPolynomial
open scoped ContDiff DirectSum
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation AngularPolynomial GreenRadialTrace

variable {dim : ℕ} [NeZero dim]

def finiteHarmonicRotationL (i j : Fin dim) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] HarmonicFiniteCoefficients dim :=
  DirectSum.lmap (fun k => harmonicSphereRotationLinear k i j)

theorem finiteHarmonicRotationL_lof (i j : Fin dim) (k : ℕ) (v : harmonicSphereSubspace dim k) :
    finiteHarmonicRotationL i j (DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k v) =
      DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k
        (harmonicSphereRotation k i j v) := by
  rw [finiteHarmonicRotationL,DirectSum.lmap_lof]
  rfl

@[expose] def smoothBallAngularDataL (i j : Fin dim) :
    smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim where
  toFun u := ⟨sphereRotationDerivative i j u.1,
    contDiff_sphereRotationDerivative i j u.1 (smoothBallData_contDiff u)⟩
  map_add' u v := by
    apply Subtype.ext
    funext z
    change sphereRotationDerivative i j (u.1+v.1) z =
      sphereRotationDerivative i j u.1 z+sphereRotationDerivative i j v.1 z
    unfold sphereRotationDerivative
    rw [fderiv_add ((smoothBallData_contDiff u).differentiable (by simp) z)
      ((smoothBallData_contDiff v).differentiable (by simp) z),add_apply]
  map_smul' c u := by
    apply Subtype.ext
    funext z
    change sphereRotationDerivative i j (c • u.1) z = c*sphereRotationDerivative i j u.1 z
    unfold sphereRotationDerivative
    rw [fderiv_const_smul ((smoothBallData_contDiff u).differentiable (by simp) z),
      smul_apply,smul_eq_mul]

theorem harmonicPolynomialRepresentative_rotation (k : ℕ) (i j : Fin dim)
    (a : harmonicSphereSubspace dim k) :
    harmonicPolynomialRepresentativeL k (harmonicSphereRotationLinear k i j a) =
      polynomialRotation i j (harmonicPolynomialRepresentativeL k a) := by
  let p : harmonicHomogeneous dim k :=
    ⟨harmonicPolynomialRepresentativeL k a,harmonicPolynomialRepresentative_mem k a⟩
  have hp : harmonicPolynomialSphereMap k p = a := by
    apply Subtype.ext
    exact polynomialSphereL2_harmonicPolynomialRepresentative k a
  apply (polynomialSphereL2_injective_degree (sphereFischerInner dim) k _ _
    (harmonicPolynomialRepresentative_mem k _) (polynomialRotation_harmonic_all k i j _ p.property)).mp
  rw [polynomialSphereL2_harmonicPolynomialRepresentative,← hp,
    harmonicSphereRotationLinear_apply_image]
  rfl

theorem harmonicFiniteSmoothL_comp_rotation (i j : Fin dim) :
    (harmonicFiniteSmoothL (dim := dim)).comp (finiteHarmonicRotationL i j) =
      (smoothBallAngularDataL i j).comp harmonicFiniteSmoothL := by
  ext k a : 2
  simp only [LinearMap.comp_apply,finiteHarmonicRotationL,DirectSum.lmap_lof,
    harmonicFiniteSmoothL,DirectSum.toModule_lof]
  apply Subtype.ext
  change polynomialEvaluation
      (harmonicPolynomialRepresentativeL k (harmonicSphereRotationLinear k i j a)) =
    sphereRotationDerivative i j (polynomialEvaluation (harmonicPolynomialRepresentativeL k a))
  rw [harmonicPolynomialRepresentative_rotation,sphereRotationDerivative_polynomialEvaluation]

theorem harmonicFiniteSmooth_rotation (i j : Fin dim) (f : HarmonicFiniteCoefficients dim) :
    (harmonicFiniteSmooth (finiteHarmonicRotationL i j f)).1 =
      sphereRotationDerivative i j (harmonicFiniteSmooth f).1 := by
  rw [← harmonicFiniteSmoothL_val,← harmonicFiniteSmoothL_val]
  exact congrArg (fun L : HarmonicFiniteCoefficients dim →ₗ[ℝ] smoothBallDataSubmodule dim =>
    (L f).1) (harmonicFiniteSmoothL_comp_rotation i j)

end CalderonN
