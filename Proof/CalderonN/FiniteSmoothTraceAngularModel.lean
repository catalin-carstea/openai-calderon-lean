module

public import Proof.CalderonN.SmoothSphereTrace
public import Proof.CalderonN.FiniteConormalModelRotation

import Mathlib.Tactic

/-! The checked finite harmonic model and its rotations inside the
smooth trace operator space. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def finiteHarmonicSmoothTraceL : HarmonicFiniteCoefficients dim →ₗ[ℝ] SmoothSphereTrace dim :=
  (smoothSphereTraceL dim).comp harmonicFiniteSmoothL

theorem finiteHarmonicSmoothTraceL_apply (f : HarmonicFiniteCoefficients dim) :
    finiteHarmonicSmoothTraceL f = smoothSphereTrace (harmonicFiniteSmooth f) := by
  apply Subtype.ext
  funext z
  exact congrFun (harmonicFiniteSmoothL_val f) z

theorem finiteHarmonicSmoothTraceL_rotation (i j : Fin dim) (f : HarmonicFiniteCoefficients dim) :
    smoothSphereTraceRotation i j (finiteHarmonicSmoothTraceL f) =
      finiteHarmonicSmoothTraceL (finiteHarmonicRotationL i j f) := by
  rw [finiteHarmonicSmoothTraceL_apply,finiteHarmonicSmoothTraceL_apply,smoothSphereTraceRotation_apply]
  exact (smoothSphereTrace_eq_iff _ _).mpr fun z _ => congrFun (harmonicFiniteSmooth_rotation i j f).symm z

theorem finiteHarmonicSmoothTraceL_sobolev (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (f : HarmonicFiniteCoefficients dim) :
    smoothSphereTraceSobolev hn s hs (finiteHarmonicSmoothTraceL f) = harmonicBoundaryFiniteL s f := by
  rw [finiteHarmonicSmoothTraceL_apply,smoothSphereTraceSobolev_apply,smoothBoundarySobolev_harmonicFiniteSmooth]

@[expose] def finiteFlatRadialTraceL : HarmonicFiniteCoefficients dim →ₗ[ℝ] SmoothSphereTrace dim :=
  (smoothSphereTraceL dim).comp flatRadialDataL

@[expose] def finiteAffineConormalTraceL (ell : X dim →L[ℝ] ℝ) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] SmoothSphereTrace dim :=
  (smoothSphereTraceL dim).comp (firstConormalDataL ell)

theorem finiteFlatRadialTraceL_rotation (i j : Fin dim) (f : HarmonicFiniteCoefficients dim) :
    smoothSphereTraceRotation i j (finiteFlatRadialTraceL f) =
      finiteFlatRadialTraceL (finiteHarmonicRotationL i j f) := by
  unfold finiteFlatRadialTraceL
  simp only [LinearMap.comp_apply]
  unfold smoothSphereTraceRotation
  rw [smoothSphereTraceMap_apply,flatRadialDataL_commutes_rotation]

theorem finiteAffineConormalTraceL_rotation (i j : Fin dim)
    (ell : X dim →L[ℝ] ℝ) (f : HarmonicFiniteCoefficients dim) :
    smoothSphereTraceRotation i j (finiteAffineConormalTraceL ell f)-
        finiteAffineConormalTraceL ell (finiteHarmonicRotationL i j f) =
      finiteAffineConormalTraceL (ell.comp (ballRotationGeneratorL i j)) f := by
  unfold finiteAffineConormalTraceL
  simp only [LinearMap.comp_apply]
  unfold smoothSphereTraceRotation
  rw [smoothSphereTraceMap_apply,← map_sub]
  apply Subtype.ext
  funext z
  exact firstConormalDataL_components_rotation i j ell f z.2

theorem finiteAffineConormalTraceL_double_rotation (i j k l : Fin dim)
    (ell : X dim →L[ℝ] ℝ) (f : HarmonicFiniteCoefficients dim) :
    let J₁ := finiteHarmonicRotationL i j
    let J₂ := finiteHarmonicRotationL k l
    let K₁ := smoothSphereTraceRotation i j
    let K₂ := smoothSphereTraceRotation k l
    let L := finiteAffineConormalTraceL ell
    K₂ (K₁ (L f)-L (J₁ f))-(K₁ (L (J₂ f))-L (J₁ (J₂ f))) =
      finiteAffineConormalTraceL ((ell.comp (ballRotationGeneratorL i j)).comp (ballRotationGeneratorL k l)) f := by
  dsimp only
  rw [finiteAffineConormalTraceL_rotation,finiteAffineConormalTraceL_rotation,finiteAffineConormalTraceL_rotation]

end CalderonN
