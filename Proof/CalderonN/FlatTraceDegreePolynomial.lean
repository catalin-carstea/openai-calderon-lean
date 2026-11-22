module

public import Proof.CalderonN.SmoothConormalTraceOperators
public import Proof.CalderonN.FlatTranslationRotation

import Proof.CalderonN.PolynomialBallGreenPairing
import Mathlib.Tactic

/-! The exact flat radial derivative on coordinate multiples, obtained
by harmonic replacement of the two homogeneous degrees. -/

public section

noncomputable section
open Set Metric MvPolynomial
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon
  SphereHarmonic AngularPolynomial GreenRadialTrace SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothCoordinateData (i : Fin dim) : SmoothData dim :=
  ⟨fun z => z i,(EuclideanSpace.proj (𝕜:=ℝ) i).contDiff⟩

@[expose] def smoothPolynomialData (p : MvPolynomial (Fin dim) ℝ) : SmoothData dim :=
  ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩

theorem negativeBallDivergence_flat_polynomialEvaluation (p : MvPolynomial (Fin dim) ℝ)
    (z : X dim) :
    negativeBallDivergence (fun _ => (1 : Mat dim)) (polynomialEvaluation p) z =
      -polynomialEvaluation (laplacian p) z := by
  classical
  unfold negativeBallDivergence Elliptic.Lop
  change -(∑ i,coordDeriv i (fun x => ∑ j,(1 : Mat dim) i j*
    coordDeriv j (polynomialEvaluation p) x) z) = _
  have h (i : Fin dim) : (fun x => ∑ j,(1 : Mat dim) i j*coordDeriv j (polynomialEvaluation p) x) =
      coordDeriv i (polynomialEvaluation p) := by
    funext x
    simp [Matrix.one_apply,ite_mul]
  simp_rw [h,coordDeriv_polynomialEvaluation]
  unfold polynomialEvaluation laplacian
  rw [map_sum]

theorem smoothSphereTaylor_flat_degree_polynomial
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (k : ℕ) (p : MvPolynomial (Fin dim) ℝ) (hp : p ∈ harmonicHomogeneous dim k) :
    let B := (LinearMap.fst ℝ _ _).comp
      ((LinearMap.snd ℝ _ _).comp (smoothSphereTaylorResponses hA hEll S))
    B (smoothSphereTrace (smoothPolynomialData p)) =
      (k : ℝ) • smoothSphereTrace (smoothPolynomialData p) := by
  dsimp only
  simp only [LinearMap.comp_apply,LinearMap.fst_apply,LinearMap.snd_apply,smoothSphereTaylorResponses_apply]
  let f := smoothPolynomialData p
  let u := S f
  have hflat (x : X dim) (_ : x ∈ ball (0 : X dim) 1) :
      negativeBallDivergence (fun _ => (1 : Mat dim)) f.1 x = 0 := by
    change negativeBallDivergence (fun _ => (1 : Mat dim)) (polynomialEvaluation p) x = _
    rw [negativeBallDivergence_flat_polynomialEvaluation,hp.2]
    simp [polynomialEvaluation]
  have hEq := eqOn_closedUnitBall_of_equal_ball_forcing contDiff_const
    (uniformlyEllipticOn_const_one_one (n := Fin dim) (fixedBallOpens dim : Set (X dim)))
    (fun _ _ => rfl) u.flat f (fun x hx => (u.flatEquation hx).trans (hflat x hx).symm) u.flatTrace
  apply Subtype.ext
  funext z
  change fderiv ℝ u.flat.1 z z = (k:ℝ)*polynomialEvaluation p z
  exact (eqOn_radialDerivative_of_eqOn_closedUnitBall hEq z.2).trans
    (radialDerivative_homogeneous_polynomialEvaluation k p hp.1 z)

theorem smoothSphereTaylor_flat_degree_coordinate
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (k : ℕ) (i : Fin dim) (p : MvPolynomial (Fin dim) ℝ) (hp : p ∈ harmonicHomogeneous dim k)
    (z : ↥(standardSphere dim)) :
    let B := (LinearMap.fst ℝ _ _).comp
      ((LinearMap.snd ℝ _ _).comp (smoothSphereTaylorResponses hA hEll S))
    let R := coordinateHarmonicRaising k i p
    let c := (2*(k:ℝ)+(dim:ℝ)-2)⁻¹
    (B (smoothSphereTraceMul (smoothCoordinateData i) (smoothSphereTrace (smoothPolynomialData p)))).1 z =
      ((k:ℝ)+1)*polynomialEvaluation R z+((k:ℝ)-1)*(c*polynomialEvaluation (pderiv i p) z) := by
  dsimp only
  let B := (LinearMap.fst ℝ _ _).comp
    ((LinearMap.snd ℝ _ _).comp (smoothSphereTaylorResponses hA hEll S))
  let R := coordinateHarmonicRaising k i p
  let c := (2*(k:ℝ)+(dim:ℝ)-2)⁻¹
  have hSplit :
      smoothSphereTraceMul (smoothCoordinateData i) (smoothSphereTrace (smoothPolynomialData p)) =
        smoothSphereTrace (smoothPolynomialData R)+c • smoothSphereTrace (smoothPolynomialData (pderiv i p)) := by
    apply Subtype.ext
    funext w
    rw [smoothSphereTraceMul_apply]
    change w.1 i*polynomialEvaluation p w =
      polynomialEvaluation R w+c*polynomialEvaluation (pderiv i p) w
    exact polynomialEvaluation_mul_coordinate_split k i p w w.2
  change (B (smoothSphereTraceMul (smoothCoordinateData i)
    (smoothSphereTrace (smoothPolynomialData p)))).1 z = _
  rw [hSplit,map_add,map_smul,smoothSphereTaylor_flat_degree_polynomial hA hEll S (k+1) R
    (coordinateHarmonicRaising_mem k i p hp)]
  have hLower : (B (smoothSphereTrace (smoothPolynomialData (pderiv i p)))).1 z =
      ((k:ℝ)-1)*polynomialEvaluation (pderiv i p) z := by
    cases k with
    | zero =>
      have hP : pderiv i p = 0 := by rw [eq_C_of_mem_harmonicHomogeneous_zero hp]; simp
      have hZ : smoothSphereTrace (smoothPolynomialData (dim:=dim) 0) = 0 := by
        apply Subtype.ext
        funext w
        change polynomialEvaluation (n:=dim) 0 w = 0
        simp [polynomialEvaluation]
      rw [hP,hZ,map_zero]
      change 0 = _ * polynomialEvaluation (n:=dim) 0 z
      simp [polynomialEvaluation]
    | succ l =>
      rw [smoothSphereTaylor_flat_degree_polynomial hA hEll S l _
        (pderiv_harmonicHomogeneous_succ l i p hp)]
      change (l:ℝ)*polynomialEvaluation (pderiv i p) z =
        ((l+1:ℕ)-(1:ℝ))*polynomialEvaluation (pderiv i p) z
      push_cast
      ring
  change ((k+1:ℕ):ℝ)*polynomialEvaluation R z+
      c*(B (smoothSphereTrace (smoothPolynomialData (pderiv i p)))).1 z = _
  rw [hLower,Nat.cast_add,Nat.cast_one]
  ring

end CalderonN
