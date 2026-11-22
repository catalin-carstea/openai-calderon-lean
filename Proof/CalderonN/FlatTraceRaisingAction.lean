module

public import Proof.CalderonN.FlatTraceDegreePolynomial
public import Proof.CalderonN.SmoothTraceGaussAdjoint

import Mathlib.Tactic

/-! The flat translation component in the actual Gauss formula is the
harmonic derivative adjoint used by the angular model. -/

public section

noncomputable section
open Set Metric MvPolynomial
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon
  SphereHarmonic AngularPolynomial GreenRadialTrace SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothAxisVelocity (i : Fin dim) : SmoothBallVelocity dim :=
  ⟨fun _ => axis i,contDiff_const⟩

theorem smoothVelocityNormal_axis (i : Fin dim) :
    (smoothVelocityNormal (smoothAxisVelocity i)).1 = (smoothCoordinateData i).1 := by
  funext z
  change ⟪z,axis i⟫_ℝ = z i
  simp [axis,EuclideanSpace.inner_single_right]

theorem smoothSphereVelocityTangent_axis_apply (i : Fin dim) (f : SmoothData dim)
    (z : ↥(standardSphere dim)) :
    (smoothSphereVelocityTangent (smoothAxisVelocity i) (smoothSphereTrace f)).1 z =
      ∑ j,sphereRotationDerivative j i (fun x => f.1 x*x j) z := by
  classical
  rw [smoothSphereVelocityTangent_apply]
  apply Finset.sum_congr rfl
  intro j _
  have h (k : Fin dim) : (fun x => f.1 x*(x j*(smoothAxisVelocity i).1 x k)) =
      if k=i then (fun x => f.1 x*x j) else 0 := by
    funext x
    by_cases hki : k=i
    · subst k; simp [smoothAxisVelocity,axis]
    · simp [smoothAxisVelocity,axis,PiLp.single_apply,hki,Ne.symm hki]
  simp_rw [h]
  have hR (k : Fin dim) :
      sphereRotationDerivative j k (if k=i then (fun x => f.1 x*x j) else 0) z =
        if k=i then sphereRotationDerivative j i (fun x => f.1 x*x j) z else 0 := by
    by_cases hk : k = i
    · subst k; simp
    · simp [hk,sphereRotationDerivative]
  simp [hR]

theorem smoothSphereGaussAdjoint_flat_axis_homogeneous (hn : 3 ≤ dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (k : ℕ) (i : Fin dim) (p : MvPolynomial (Fin dim) ℝ) (hp : p ∈ harmonicHomogeneous dim k) :
    let B := (LinearMap.fst ℝ _ _).comp
      ((LinearMap.snd ℝ _ _).comp (smoothSphereTaylorResponses hA hEll S))
    smoothSphereGaussAdjoint B (smoothAxisVelocity i) (smoothSphereTrace (smoothPolynomialData p)) =
      smoothSphereTrace (smoothPolynomialData (sphereDerivativeAdjoint k i p)) := by
  dsimp only
  let B := (LinearMap.fst ℝ _ _).comp
    ((LinearMap.snd ℝ _ _).comp (smoothSphereTaylorResponses hA hEll S))
  let R := coordinateHarmonicRaising k i p
  let c := (2*(k:ℝ)+(dim:ℝ)-2)⁻¹
  have hCoord : smoothVelocityNormal (smoothAxisVelocity i) = smoothCoordinateData i :=
    Subtype.ext (smoothVelocityNormal_axis i)
  apply Subtype.ext
  funext z
  change (B (smoothSphereTraceMul (smoothVelocityNormal (smoothAxisVelocity i))
    (smoothSphereTrace (smoothPolynomialData p)))).1 z-
    (smoothSphereVelocityTangent (smoothAxisVelocity i) (smoothSphereTrace (smoothPolynomialData p))).1 z =
      polynomialEvaluation (sphereDerivativeAdjoint k i p) z
  rw [hCoord,smoothSphereTaylor_flat_degree_coordinate hA hEll S k i p hp z,
    smoothSphereVelocityTangent_axis_apply]
  change ((k:ℝ)+1)*polynomialEvaluation R z+((k:ℝ)-1)*(c*polynomialEvaluation (pderiv i p) z)-
    (∑ j,sphereRotationDerivative j i (fun x => polynomialEvaluation p x*x j) z) = _
  rw [sphere_rotation_sum_mul_coordinate k i p hp.1 z z.2,
    polynomialEvaluation_mul_coordinate_split k i p z z.2,
    sphereDerivativeAdjoint_eq_coordinateRaising k i p hp]
  change _ = eval (euclideanCoordinates dim (z : X dim)) (C ((dim:ℝ)+2*(k:ℝ))*R)
  rw [map_mul,eval_C]
  change _ = ((dim:ℝ)+2*(k:ℝ))*polynomialEvaluation R z
  have hd : (3:ℝ) ≤ dim := by exact_mod_cast hn
  have hDen : 0 < 2*(k:ℝ)+(dim:ℝ)-2 := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have hC : c*(2*(k:ℝ)+(dim:ℝ)-2) = 1 := inv_mul_cancel₀ hDen.ne'
  have hL : c*polynomialEvaluation (pderiv i p) z*
      (2*(k:ℝ)+(dim:ℝ)-2) = polynomialEvaluation (pderiv i p) z := by
    rw [mul_right_comm,hC,one_mul]
  linarith only [hL]

end CalderonN
