module

public import Proof.CalderonN.FiniteConormalResponseLinear
public import Proof.CalderonN.FiniteAngularDriftModel

import Proof.CalderonN.BallRotationCalculus
import Mathlib.Tactic

/-! Rotations commute with the degree multiplier and rotate the
covector in the first conormal Taylor coefficient. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def flatRadialDataL : HarmonicFiniteCoefficients dim →ₗ[ℝ] smoothBallDataSubmodule dim :=
  smoothBallRadialDataL.comp harmonicFiniteSmoothL

@[expose] def driftRadialDataL (ell : X dim →L[ℝ] ℝ) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] smoothBallDataSubmodule dim :=
  smoothBallRadialDataL.comp (harmonicFiniteDriftVariationSmoothL ell)

@[expose] def firstConormalDataL (ell : X dim →L[ℝ] ℝ) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] smoothBallDataSubmodule dim :=
  (smoothBallDataMulL ⟨ell,ell.contDiff⟩).comp flatRadialDataL + driftRadialDataL ell

theorem flatRadialDataL_apply (f : HarmonicFiniteCoefficients dim) :
    (flatRadialDataL f).1 = fun z => fderiv ℝ (harmonicFiniteSmooth f).1 z z := by
  rw [flatRadialDataL,LinearMap.comp_apply,smoothBallRadialDataL_val,harmonicFiniteSmoothL_val]

theorem driftRadialDataL_apply (ell : X dim →L[ℝ] ℝ) (f : HarmonicFiniteCoefficients dim) :
    (driftRadialDataL ell f).1 = fun z => fderiv ℝ (harmonicFiniteDriftVariationSmooth ell f).1 z z := by
  rw [driftRadialDataL,LinearMap.comp_apply,smoothBallRadialDataL_val,harmonicFiniteDriftVariationSmoothL_val]

theorem firstConormalDataL_apply (ell : X dim →L[ℝ] ℝ) (f : HarmonicFiniteCoefficients dim) :
    (firstConormalDataL ell f).1 = fun z => ell z*fderiv ℝ (harmonicFiniteSmooth f).1 z z+
      fderiv ℝ (harmonicFiniteDriftVariationSmooth ell f).1 z z := by
  rw [firstConormalDataL,LinearMap.add_apply,LinearMap.comp_apply]
  funext z
  change (smoothBallDataMulL ⟨ell,ell.contDiff⟩ (flatRadialDataL f)).1 z+(driftRadialDataL ell f).1 z = _
  rw [smoothBallDataMulL_apply,flatRadialDataL_apply,driftRadialDataL_apply]

theorem flatRadialDataL_commutes_rotation (i j : Fin dim) (f : HarmonicFiniteCoefficients dim) :
    smoothBallAngularDataL i j (flatRadialDataL f) =
      flatRadialDataL (finiteHarmonicRotationL i j f) := by
  apply Subtype.ext
  funext z
  change sphereRotationDerivative i j (flatRadialDataL f).1 z = _
  rw [flatRadialDataL_apply,flatRadialDataL_apply,harmonicFiniteSmooth_rotation]
  exact sphereRotationDerivative_comm_radial i j (harmonicFiniteSmooth f).2 z

theorem firstConormalDataL_components_rotation (i j : Fin dim)
    (ell : X dim →L[ℝ] ℝ) (f : HarmonicFiniteCoefficients dim) :
    EqOn (smoothBallAngularDataL i j (firstConormalDataL ell f)-
      firstConormalDataL ell (finiteHarmonicRotationL i j f)).1
      (firstConormalDataL (ell.comp (ballRotationGeneratorL i j)) f).1 (standardSphere dim) := by
  intro z hz
  let A := flatRadialDataL f
  let Q := driftRadialDataL ell f
  let Qθ := driftRadialDataL ell (finiteHarmonicRotationL i j f)
  let K := smoothBallAngularDataL i j
  let L := smoothBallDataMulL (⟨ell,ell.contDiff⟩ : SmoothData dim)
  have hC (g : HarmonicFiniteCoefficients dim) : firstConormalDataL ell g =
      L (flatRadialDataL g)+driftRadialDataL ell g := rfl
  rw [hC f,hC (finiteHarmonicRotationL i j f),map_add,← flatRadialDataL_commutes_rotation]
  change (K (L A)).1 z+(K Q).1 z-((L (K A)).1 z+Qθ.1 z) = _
  have hKℓ : sphereRotationDerivative i j (⇑ell) z =
      (ell.comp (ballRotationGeneratorL i j)) z := by
    rw [sphereRotationDerivative,ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,
      ballRotationGeneratorL_apply]
  have hL : (K (L A)).1 z = (ell.comp (ballRotationGeneratorL i j)) z*A.1 z+ell z*(K A).1 z := by
    change sphereRotationDerivative i j (L A).1 z = _
    rw [show (L A).1 = fun w => ell w*A.1 w from smoothBallDataMulL_apply _ _,
      sphereRotationDerivative_mul i j ell.contDiff (smoothBallData_contDiff A),hKℓ]
    rfl
  have hQ : (K Q).1 z-Qθ.1 z = (driftRadialDataL (ell.comp (ballRotationGeneratorL i j)) f).1 z := by
    change sphereRotationDerivative i j (driftRadialDataL ell f).1 z -
      (driftRadialDataL ell (finiteHarmonicRotationL i j f)).1 z = _
    rw [driftRadialDataL_apply,driftRadialDataL_apply,driftRadialDataL_apply]
    exact eqOn_radial_angular_harmonicFiniteDriftVariation i j ell f hz
  rw [hL,show (L (K A)).1 z = ell z*(K A).1 z from congrFun (smoothBallDataMulL_apply _ _) z]
  rw [firstConormalDataL_apply]
  have hA := congrFun (flatRadialDataL_apply f) z
  have hQ' := congrFun (driftRadialDataL_apply (ell.comp (ballRotationGeneratorL i j)) f) z
  change A.1 z = _ at hA
  change _ = (ell.comp (ballRotationGeneratorL i j)) z*fderiv ℝ (harmonicFiniteSmooth f).1 z z+
    fderiv ℝ (harmonicFiniteDriftVariationSmooth (ell.comp (ballRotationGeneratorL i j)) f).1 z z
  rw [← hA,← hQ',← hQ]
  ring

end CalderonN
