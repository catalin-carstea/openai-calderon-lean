module

public import Proof.CalderonN.FiniteRadialResponseLinear
public import Proof.CalderonN.FiniteHarmonicRotation
public import Proof.CalderonN.SmoothBoundaryHilbert
public import Proof.CalderonN.AngularRadialWeight

import Mathlib.Tactic

/-! Compose the actual radial solution with Gauss' weight, keeping
linearity on the same finite Dirichlet inputs. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

def smoothBallDataMulL (m : SmoothData dim) :
    smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim where
  toFun u := ⟨fun z => m.1 z*u.1 z,m.2.mul (smoothBallData_contDiff u)⟩
  map_add' u v := by
    apply Subtype.ext
    funext z
    change m.1 z*(u.1 z+v.1 z) = m.1 z*u.1 z+m.1 z*v.1 z
    ring
  map_smul' a u := by
    apply Subtype.ext
    funext z
    change m.1 z*(a*u.1 z) = a*(m.1 z*u.1 z)
    ring

theorem smoothBallDataMulL_apply (m : SmoothData dim) (u : smoothBallDataSubmodule dim) :
    (smoothBallDataMulL m u).1 = fun z => m.1 z*u.1 z := by
  unfold smoothBallDataMulL
  rfl

theorem smoothBallDataMulL_congr (m : SmoothData dim) (u v : smoothBallDataSubmodule dim)
    (h : EqOn u.1 v.1 (standardSphere dim)) :
    EqOn (smoothBallDataMulL m u).1 (smoothBallDataMulL m v).1 (standardSphere dim) := by
  intro z hz
  exact congrArg (m.1 z * ·) (h hz)

theorem smoothBallAngularDataL_congr (i j : Fin dim) (u v : smoothBallDataSubmodule dim)
    (h : EqOn u.1 v.1 (standardSphere dim)) :
    EqOn (smoothBallAngularDataL i j u).1 (smoothBallAngularDataL i j v).1 (standardSphere dim) :=
  EqOn.sphereRotationDerivative h (smoothBallData_contDiff u) (smoothBallData_contDiff v) i j

def finiteSphereMappedRadialResponseL (hn : 3 ≤ dim)
    (B : smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim)
    (hB : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → EqOn (B u).1 (B v).1 (standardSphere dim))
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hH : ∀ f, EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1)) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim :=
  (sphereSobolevZeroEquiv (dim:=dim)).symm.toLinearEquiv.toLinearMap.comp
    (finiteMappedRadialResponseL hn 0 (by norm_num) B hB ha hEll b hT hH)

theorem finiteSphereMappedRadialResponseL_apply (hn : 3 ≤ dim)
    (B : smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim)
    (hB : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → EqOn (B u).1 (B v).1 (standardSphere dim))
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hH : ∀ f, EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1))
    (f : HarmonicFiniteCoefficients dim) :
    finiteSphereMappedRadialResponseL hn B hB ha hEll b hT hH f =
      smoothBoundaryLiftL hn (B (smoothBallRadialDataL ⟨(b f).1,(b f).2⟩)) := by
  unfold finiteSphereMappedRadialResponseL smoothBoundaryLiftL
  rw [LinearMap.comp_apply,LinearMap.comp_apply,finiteMappedRadialResponseL_apply]

end CalderonN
