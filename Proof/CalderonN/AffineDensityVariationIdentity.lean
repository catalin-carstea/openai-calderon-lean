module

public import Proof.CalderonN.SmoothTraceFlatDegree

import Proof.CalderonN.SmoothStrongBallEstimates
import Mathlib.Tactic

/-! For the affine scalar density, the first Dirichlet variation is
half of the difference between harmonic extension of the boundary
product and the product of the linear density with the harmonic lift. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim]

private theorem coordinate_product_smooth {u v : X dim → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (i : I dim) :
    coordDeriv i (u*v) = fun z => coordDeriv i u z*v z+u z*coordDeriv i v z := by
  funext z
  unfold coordDeriv
  have h := ((hu.differentiable (by simp) z).hasFDerivAt.mul
    (hv.differentiable (by simp) z).hasFDerivAt).fderiv
  change fderiv ℝ (u*v) z (axis i) = _
  rw [h]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

private theorem contDiff_coordinateDeriv {u : X dim → ℝ} (hu : ContDiff ℝ ∞ u) (i : I dim) :
    ContDiff ℝ ∞ (coordDeriv i u) :=
  (hu.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

private theorem coordDeriv_densityLinear (ell : X dim →L[ℝ] ℝ) (i : I dim) :
    coordDeriv i (⇑ell) = fun _ => ell (axis i) := by
  funext z
  rw [coordDeriv,ell.fderiv]

private theorem flat_negativeBallDivergence (u : X dim → ℝ) (z : X dim) :
    negativeBallDivergence (fun _ => (1 : Mat dim)) u z =
      -(∑ i : I dim,coordDeriv i (coordDeriv i u) z) := by
  classical
  change -(∑ i : I dim,coordDeriv i (fun w => ∑ j : I dim,(1 : Mat dim) i j*coordDeriv j u w) z) = _
  have h (i : I dim) : (fun w => ∑ j : I dim,(1 : Mat dim) i j*coordDeriv j u w) = coordDeriv i u := by
    funext w
    simp [Matrix.one_apply,ite_mul]
  simp only [h]

private theorem linear_negativeBallDivergence (ell : X dim →L[ℝ] ℝ)
    (u : SmoothData dim) (z : X dim) :
    negativeBallDivergence (fun w => ell w • (1 : Mat dim)) u.1 z =
      ell z*negativeBallDivergence (fun _ => (1 : Mat dim)) u.1 z-
        ∑ i : I dim,ell (axis i)*coordDeriv i u.1 z := by
  classical
  change -(∑ i : I dim,coordDeriv i (fun w => ∑ j : I dim,
    (ell w • (1 : Mat dim)) i j*coordDeriv j u.1 w) z) = _
  have h (i : I dim) : (fun w => ∑ j : I dim,
      (ell w • (1 : Mat dim)) i j*coordDeriv j u.1 w) = (⇑ell)*(coordDeriv i u.1) := by
    funext w
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite,mul_zero,mul_one,ite_mul,
      zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,Pi.mul_apply]
  simp only [h,coordinate_product_smooth ell.contDiff (contDiff_coordinateDeriv u.2 _),
    coordDeriv_densityLinear,flat_negativeBallDivergence,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

private theorem flat_product_negativeBallDivergence (ell : X dim →L[ℝ] ℝ)
    (u : SmoothData dim) (z : X dim) :
    negativeBallDivergence (fun _ => (1 : Mat dim)) ((⇑ell)*u.1) z =
      ell z*negativeBallDivergence (fun _ => (1 : Mat dim)) u.1 z-
        2*∑ i : I dim,ell (axis i)*coordDeriv i u.1 z := by
  simp only [flat_negativeBallDivergence]
  have h (i : I dim) : coordDeriv i (coordDeriv i ((⇑ell)*u.1)) z =
      2*(ell (axis i)*coordDeriv i u.1 z)+ell z*coordDeriv i (coordDeriv i u.1) z := by
    rw [coordinate_product_smooth ell.contDiff u.2,coordDeriv_densityLinear]
    let f (w : X dim) := ell (axis i)*u.1 w
    let g (w : X dim) := ell w*coordDeriv i u.1 w
    change coordDeriv i (f+g) z = _
    have hf : ContDiff ℝ ∞ f := contDiff_const.mul u.2
    have hg : ContDiff ℝ ∞ g := ell.contDiff.mul (contDiff_coordinateDeriv u.2 i)
    have hAdd : coordDeriv i (f+g) z = coordDeriv i f z+coordDeriv i g z := by
      unfold coordDeriv
      rw [fderiv_add ((hf.differentiable (by simp)) z) ((hg.differentiable (by simp)) z),
        ContinuousLinearMap.add_apply]
    have hf' : coordDeriv i f z = ell (axis i)*coordDeriv i u.1 z := by
      change coordDeriv i ((fun _ : X dim => ell (axis i))*u.1) z = _
      rw [coordinate_product_smooth contDiff_const u.2]
      simp [coordDeriv]
    have hg' : coordDeriv i g z =
        ell (axis i)*coordDeriv i u.1 z+ell z*coordDeriv i (coordDeriv i u.1) z := by
      change coordDeriv i ((⇑ell)*coordDeriv i u.1) z = _
      simp only [coordinate_product_smooth ell.contDiff (contDiff_coordinateDeriv u.2 i),coordDeriv_densityLinear]
    rw [hAdd,hf',hg']
    ring
  simp only [h,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

variable [Nontrivial (Fin dim)]

theorem smoothTrace_affine_density_radial_formula
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (f : SmoothData dim) :
    let B := smoothTraceFlatDegree hA hEll S
    let L := smoothSphereTraceMul ⟨ell,ell.contDiff⟩
    smoothSphereTrace (smoothBallRadialDerivative (S f).first) =
      (1/2:ℝ) • (B (L (smoothSphereTrace f))-L (B (smoothSphereTrace f))-L (smoothSphereTrace f)) := by
  dsimp only
  let u := (S f).flat
  let E : SmoothData dim := ⟨(⇑ell)*f.1,ell.contDiff.mul f.2⟩
  let q := (S E).flat
  let v : SmoothData dim := ⟨(⇑ell)*u.1,ell.contDiff.mul u.2⟩
  let w : SmoothData dim := ⟨(1/2:ℝ) • (q.1-v.1), (q.2.sub v.2).const_smul (1/2:ℝ)⟩
  have hT : EqOn w.1 (0 : X dim → ℝ) (standardSphere dim) := by
    intro z hz
    change (1/2:ℝ)*((S E).flat.1 z-ell z*(S f).flat.1 z) = 0
    rw [(S E).flatTrace hz,(S f).flatTrace hz]
    change (1/2:ℝ)*(ell z*f.1 z-ell z*f.1 z) = 0
    ring
  have hEq : EqOn (negativeBallDivergence (fun _ => (1 : Mat dim)) w.1)
      (negativeBallDivergence (fun _ => (1 : Mat dim)) (S f).first.1) (ball (0:X dim) 1) := by
    intro z hz
    let D := fun _ : X dim => (1 : Mat dim)
    let U : SmoothData dim := ⟨q.1-v.1,q.2.sub v.2⟩
    change negativeBallDivergence D ((1/2:ℝ) • U.1) z = _
    rw [negativeBallDivergence_const_smul_solution contDiff_const U,
      show U.1 = q.1-v.1 from rfl,negativeBallDivergence_sub_solution contDiff_const q v,
      (S E).flatEquation hz,(S f).firstEquation hz]
    change (1/2:ℝ)*(0-negativeBallDivergence D ((⇑ell)*u.1) z) =
      -negativeBallDivergence (fun w => ell w • (1 : Mat dim)) u.1 z
    rw [linear_negativeBallDivergence ell u,flat_product_negativeBallDivergence ell u,(S f).flatEquation hz]
    simp only [Pi.zero_apply,mul_zero]
    ring
  have hBall := eqOn_closedUnitBall_of_equal_ball_forcing contDiff_const
    (uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim)))
    (fun _ _ => rfl) w (S f).first hEq (fun _ hz => (hT hz).trans ((S f).firstTrace hz).symm)
  have hMul : smoothSphereTraceMul ⟨ell,ell.contDiff⟩ (smoothSphereTrace f) = smoothSphereTrace E := by
    apply Subtype.ext
    funext z
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply]
    rfl
  rw [hMul,smoothTraceFlatDegree_apply,smoothTraceFlatDegree_apply]
  apply Subtype.ext
  funext z
  change fderiv ℝ (S f).first.1 z z = _
  have hRad : fderiv ℝ w.1 (z:X dim) (z:X dim) = fderiv ℝ (S f).first.1 (z:X dim) (z:X dim) :=
    eqOn_radialDerivative_of_eqOn_closedUnitBall hBall z.2
  rw [← hRad]
  have hProd (p : X dim) :
      fderiv ℝ v.1 p p = ell p*u.1 p+ell p*fderiv ℝ u.1 p p := by
    change fderiv ℝ ((⇑ell)*u.1) p p = _
    rw [(ell.hasFDerivAt.mul (u.2.differentiable (by simp) p).hasFDerivAt).fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  have hd (z : X dim) : fderiv ℝ w.1 z z =
      (1/2:ℝ)*(fderiv ℝ q.1 z z-fderiv ℝ v.1 z z) := by
    have h := (((q.2.differentiable (by simp) z).hasFDerivAt.sub
      (v.2.differentiable (by simp) z).hasFDerivAt).const_smul (1/2:ℝ)).fderiv
    exact congrArg (fun L : X dim →L[ℝ] ℝ => L z) h
  rw [hd,hProd,(S f).flatTrace z.2]
  have hE := smoothSphereTraceMul_apply ⟨ell,ell.contDiff⟩ (smoothSphereTrace (S f).degree) z
  change (smoothSphereTraceMul ⟨ell,ell.contDiff⟩ (smoothSphereTrace (S f).degree)).1 z =
    ell z*fderiv ℝ u.1 z z at hE
  change (1/2:ℝ)*(fderiv ℝ q.1 z z-(ell z*f.1 z+ell z*fderiv ℝ u.1 z z)) =
    (1/2:ℝ)*((smoothSphereTrace (S E).degree).1 z-
      (smoothSphereTraceMul ⟨ell,ell.contDiff⟩ (smoothSphereTrace (S f).degree)).1 z-
        (smoothSphereTrace E).1 z)
  rw [hE]
  change _ = (1/2:ℝ)*(fderiv ℝ q.1 z z-ell z*fderiv ℝ u.1 z z-ell z*f.1 z)
  ring

end CalderonN
