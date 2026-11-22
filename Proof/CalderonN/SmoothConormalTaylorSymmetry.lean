module

public import Proof.CalderonN.SmoothConormalTaylorSolutions

import Mathlib.Tactic

/-! The conormal Taylor remainder and the flat degree operator are
symmetric on the genuine smooth boundary solutions. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem conormalTaylorSolutions_degree_symmetric
    {A : X dim → Mat dim} {ell : X dim →L[ℝ] ℝ} {f g : SmoothData dim}
    (U : ConormalTaylorSolutions A ell f) (V : ConormalTaylorSolutions A ell g) :
    ⟪smoothSphereLift U.degree.1 U.degree.2,smoothSphereLift g.1 g.2⟫_ℝ =
      ⟪smoothSphereLift f.1 f.2,smoothSphereLift V.degree.1 V.degree.2⟫_ℝ := by
  rw [smoothSphereLift_inner,smoothSphereLift_inner]
  have h := integral_smoothBallConormal_symm (A := fun _ => (1 : Mat dim)) contDiff_const
    (fun _ _ => Matrix.isSymm_one) f g U.flat V.flat U.flatEquation V.flatEquation U.flatTrace V.flatTrace
  have hd (u : SmoothData dim) (z : X dim) :
      smoothBallConormal (fun _ => (1 : Mat dim)) u.1 z = fderiv ℝ u.1 z z := by
    simpa only [smoothBallConormal,one_smul,one_mul] using inner_smoothBallFlux_scalar (fun _ => 1) u.1 z
  simp_rw [hd] at h
  exact h

theorem conormalTaylorSolutions_remainder_symmetric (hn : 3 ≤ dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, (A z).IsSymm)
    {ell : X dim →L[ℝ] ℝ} {f g : SmoothData dim}
    (U : ConormalTaylorSolutions A ell f) (V : ConormalTaylorSolutions A ell g) (r : ℝ) :
    ⟪smoothSphereLift (U.remainder hA r).1 (U.remainder hA r).2,smoothSphereLift g.1 g.2⟫_ℝ =
      ⟪smoothSphereLift f.1 f.2,smoothSphereLift (V.remainder hA r).1 (V.remainder hA r).2⟫_ℝ := by
  let L := smoothBoundaryLiftL (dim:=dim) hn
  let Z (x : SmoothData dim) := smoothSphereLift x.1 x.2
  let C {h : SmoothData dim} (W : ConormalTaylorSolutions A ell h) : SmoothData dim :=
    ⟨smoothBallConormal A W.actual.1,contDiff_smoothBallConormal hA W.actual⟩
  have hZ {h : SmoothData dim} (W : ConormalTaylorSolutions A ell h) :
      Z (W.remainder hA r) = Z (C W)-Z W.degree-r • Z W.affineConormal := by
    let R : smoothBallDataSubmodule dim := ⟨(C W).1,(C W).2⟩
    let B : smoothBallDataSubmodule dim := ⟨W.degree.1,W.degree.2⟩
    let Q : smoothBallDataSubmodule dim := ⟨W.affineConormal.1,W.affineConormal.2⟩
    have h : L (R-B-r • Q) = L R-L B-r • L Q := by rw [map_sub,map_sub,map_smul]
    change smoothSphereLift (R-B-r • Q).1 (smoothBallData_contDiff _) = _
    simpa only [L,smoothBoundaryLiftL_apply] using h
  have h₀ := conormalTaylorSolutions_degree_symmetric U V
  have h₁ : ⟪Z U.affineConormal,Z g⟫_ℝ = ⟪Z f,Z V.affineConormal⟫_ℝ := by
    simp only [Z,smoothSphereLift_inner]
    exact integral_smoothFirstConormal_symm ell f g U.flat V.flat U.first V.first
      U.flatTrace V.flatTrace U.flatEquation V.flatEquation U.firstTrace V.firstTrace
      U.firstEquation V.firstEquation
  have h₂ : ⟪Z (C U),Z g⟫_ℝ = ⟪Z f,Z (C V)⟫_ℝ := by
    simp only [Z,smoothSphereLift_inner]
    exact integral_smoothBallConormal_symm hA hSym f g U.actual V.actual
      U.actualEquation V.actualEquation U.actualTrace V.actualTrace
  change ⟪Z (U.remainder hA r),Z g⟫_ℝ = ⟪Z f,Z (V.remainder hA r)⟫_ℝ
  rw [hZ,hZ,inner_sub_left,inner_sub_left,inner_sub_right,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,h₂,h₀,h₁]

end CalderonN
