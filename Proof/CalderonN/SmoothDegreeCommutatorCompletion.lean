module

public import Proof.CalderonN.SmoothPairingCompletion

import Mathlib.Tactic

/-! A real symmetric radial remainder and the flat degree operator
give an actual skew commutator, whose finite estimate passes to smooth data. -/

public section

noncomputable section
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2050000
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SphereHarmonic
variable {dim : ℕ} [NeZero dim]

theorem abs_smooth_degree_pair_le_of_finite (hn : 3 ≤ dim)
    (T B : SmoothData dim → SmoothData dim)
    (hT : ∀ u v, ⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift v.1 v.2⟫_ℝ =
      ⟪smoothSphereLift u.1 u.2,smoothSphereLift (T v).1 (T v).2⟫_ℝ)
    (hB : ∀ u v, ⟪smoothSphereLift (B u).1 (B u).2,smoothSphereLift v.1 v.2⟫_ℝ =
      ⟪smoothSphereLift u.1 u.2,smoothSphereLift (B v).1 (B v).2⟫_ℝ)
    (C : ℝ)
    (hFin : ∀ f g : HarmonicFiniteCoefficients dim,
      let u := harmonicFiniteSmooth f
      let v := harmonicFiniteSmooth g
      |⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift (B v).1 (B v).2⟫_ℝ-
        ⟪smoothSphereLift (T (B u)).1 (T (B u)).2,smoothSphereLift v.1 v.2⟫_ℝ| ≤
        C*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖)
    (u v : SmoothData dim) :
    |⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift (B v).1 (B v).2⟫_ℝ-
      ⟪smoothSphereLift (T (B u)).1 (T (B u)).2,smoothSphereLift v.1 v.2⟫_ℝ| ≤
      C*‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u‖*
        ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) v‖ := by
  let D (x y : SmoothData dim) : SmoothData dim := ⟨x.1-y.1,x.2.sub y.2⟩
  let L := smoothBoundaryLiftL (dim:=dim) hn
  let Z (x : SmoothData dim) := smoothSphereLift x.1 x.2
  have hD (x y : SmoothData dim) : Z (D x y) = Z x-Z y := by
    let X' : smoothBallDataSubmodule dim := ⟨x.1,x.2⟩
    let Y' : smoothBallDataSubmodule dim := ⟨y.1,y.2⟩
    change smoothSphereLift (X'-Y').1 (smoothBallData_contDiff (X'-Y')) =
      smoothSphereLift X'.1 (smoothBallData_contDiff X') - smoothSphereLift Y'.1 (smoothBallData_contDiff Y')
    have hh := L.map_sub X' Y' 
    simpa only [L,smoothBoundaryLiftL_apply] using hh
  let S (u : SmoothData dim) := D (B (T u)) (T (B u))
  let S' (u : SmoothData dim) := D (T (B u)) (B (T u))
  have hA (x y : SmoothData dim) : ⟪Z (S x),Z y⟫_ℝ = ⟪Z x,Z (S' y)⟫_ℝ := by
    change ⟪Z (D (B (T x)) (T (B x))),Z y⟫_ℝ = ⟪Z x,Z (D (T (B y)) (B (T y)))⟫_ℝ
    rw [hD,hD,inner_sub_left,inner_sub_right,hB (T x) y,hT x (B y),hT (B x) y,hB x (T y)]
  have hForm (x y : SmoothData dim) : ⟪Z (S x),Z y⟫_ℝ =
      ⟪Z (T x),Z (B y)⟫_ℝ-⟪Z (T (B x)),Z y⟫_ℝ := by
    change ⟪Z (D (B (T x)) (T (B x))),Z y⟫_ℝ = _
    rw [hD,inner_sub_left,hB (T x) y]
  have hFin' (f g : HarmonicFiniteCoefficients dim) :
      |⟪Z (S (harmonicFiniteSmooth f)),finiteHarmonicSphereL hn g⟫_ℝ| ≤
        C*‖harmonicBoundaryFiniteL (1/2:ℝ) f‖*‖harmonicBoundaryFiniteL (1/2:ℝ) g‖ := by
    rw [finiteHarmonicSphereL_apply hn g,hForm]
    exact hFin f g
  rw [← hForm u v]
  exact abs_smooth_pair_le_of_finite_harmonic hn S S' hA (1/2:ℝ) (1/2:ℝ) C (by norm_num)
    (by norm_num) hFin' u v

end CalderonN
