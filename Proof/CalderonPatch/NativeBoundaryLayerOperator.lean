module

public import Proof.CalderonPatch.NativeBoundaryLayerCoefficients
public import Proof.CalderonPatch.BoundaryLayerScalar

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I axis coordDeriv MetricField laplace)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n + 1)

private theorem fderiv_tangent_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Y × ℝ → F} (hV : Differentiable ℝ V) (y : Y) (t : ℝ) (v : Y) :
    fderiv ℝ (fun w : Y => V (w,t)) y v = fderiv ℝ V (y,t) (v,0) := by
  let L := ContinuousLinearMap.inl ℝ Y ℝ
  have hA : HasFDerivAt (fun w : Y => (w,t)) L y := by
    convert L.hasFDerivAt.add_const ((0 : Y),t) using 1
    funext w
    simp [L]
  exact congrArg (fun A : Y →L[ℝ] F => A v)
    (((hV (y,t)).hasFDerivAt.comp y hA).fderiv)

private theorem deriv_normal_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Y × ℝ → F} (hV : Differentiable ℝ V) (y : Y) (t : ℝ) :
    deriv (fun r : ℝ => V (y,r)) t = fderiv ℝ V (y,t) (0,1) := by
  let L := ContinuousLinearMap.inr ℝ Y ℝ
  have hA : HasFDerivAt (fun r : ℝ => (y,r)) L t := by
    convert L.hasFDerivAt.const_add (y,(0 : ℝ)) using 1
    funext r
    simp [L]
  exact ((hV (y,t)).hasFDerivAt.comp t hA).hasDerivAt.deriv

private theorem contDiff_directional {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : E → F} (hV : ContDiff ℝ ∞ V) (v : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ V x v) :=
  (hV.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).clm_apply contDiff_const

private theorem fderiv_read_signed {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V)
    (R : ℂ →L[ℝ] ℝ) (w v : Y × ℝ) :
    fderiv ℝ (R ∘ V ∘ signedLayerCoordinates.symm) (signedLayerCoordinates w)
          (signedLayerCoordinates v) = R (fderiv ℝ V w v) := by
  have hw : signedLayerCoordinates.symm (signedLayerCoordinates w) = w :=
    signedLayerCoordinates.symm_apply_apply w
  have h₁ := R.hasFDerivAt.comp (signedLayerCoordinates w)
    ((((hV.differentiable (by simp) (signedLayerCoordinates.symm (signedLayerCoordinates w))).hasFDerivAt)).comp
      (signedLayerCoordinates w) (signedLayerCoordinates.symm.toContinuousLinearMap.hasFDerivAt))
  rw [h₁.fderiv]
  simp [hw]

private theorem coordDeriv_read_signed_first {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V)
    (R : ℂ →L[ℝ] ℝ) (y : Y) (t : ℝ) (i : I n) :
    coordDeriv i.succ (R ∘ V ∘ signedLayerCoordinates.symm) (signedLayerCoordinates (y,t)) =
      R (splitFirst V y t i) := by
  rw [coordDeriv, ← signedLayerCoordinates_axis_tangent]
  rw [fderiv_read_signed hV]
  rw [splitFirst,EuclideanSpace.basisFun_apply,← CalderonN.axis,
    fderiv_tangent_slice (hV.differentiable (by simp))]

theorem coordDeriv_read_signed_normal {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V)
    (R : ℂ →L[ℝ] ℝ) (y : Y) (t : ℝ) :
    coordDeriv 0 (R ∘ V ∘ signedLayerCoordinates.symm) (signedLayerCoordinates (y,t)) =
      R (splitNormal V y t) := by
  rw [coordDeriv, ← signedLayerCoordinates_axis_normal]
  rw [fderiv_read_signed hV,splitNormal,deriv_normal_slice (hV.differentiable (by simp))]

private theorem coordDeriv_read_signed_second {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V)
    (R : ℂ →L[ℝ] ℝ) (y : Y) (t : ℝ) (i j : I n) :
    coordDeriv i.succ (coordDeriv j.succ (R ∘ V ∘ signedLayerCoordinates.symm))
        (signedLayerCoordinates (y,t)) = R (splitSecond V y t i j) := by
  let Vj := fun w : Y × ℝ => fderiv ℝ V w (axis j,0)
  have hVj : ContDiff ℝ ∞ Vj := contDiff_directional hV _
  have he : coordDeriv j.succ (R ∘ V ∘ signedLayerCoordinates.symm) =
      R ∘ Vj ∘ signedLayerCoordinates.symm := by
    funext z
    obtain ⟨⟨a,b⟩,rfl⟩ := signedLayerCoordinates.surjective z
    rw [coordDeriv_read_signed_first hV]
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply,Vj,splitFirst,
      EuclideanSpace.basisFun_apply,axis,fderiv_tangent_slice (hV.differentiable (by simp))]
  rw [he,coordDeriv_read_signed_first hVj]
  congr 1
  simp only [splitFirst,splitSecond,EuclideanSpace.basisFun_apply,axis,Vj]
  exact congrArg (fun f : Y → ℂ => fderiv ℝ f y (EuclideanSpace.single i 1))
    (funext fun u => (fderiv_tangent_slice (hV.differentiable (by simp)) u t (axis j)).symm)

private theorem coordDeriv_read_signed_normalSecond {V : Y × ℝ → ℂ}
    (hV : ContDiff ℝ ∞ V) (R : ℂ →L[ℝ] ℝ) (y : Y) (t : ℝ) :
    coordDeriv 0 (coordDeriv 0 (R ∘ V ∘ signedLayerCoordinates.symm))
        (signedLayerCoordinates (y,t)) = R (splitNormalSecond V y t) := by
  let V₀ := fun w : Y × ℝ => fderiv ℝ V w (0,1)
  have hV₀ : ContDiff ℝ ∞ V₀ := contDiff_directional hV _
  have he : coordDeriv 0 (R ∘ V ∘ signedLayerCoordinates.symm) =
      R ∘ V₀ ∘ signedLayerCoordinates.symm := by
    funext z
    obtain ⟨⟨a,b⟩,rfl⟩ := signedLayerCoordinates.surjective z
    rw [coordDeriv_read_signed_normal hV]
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply,V₀,splitNormal,
      deriv_normal_slice (hV.differentiable (by simp))]
  rw [he,coordDeriv_read_signed_normal hV₀]
  congr 1
  exact congrArg (fun f : ℝ → ℂ => deriv f t)
    (funext fun r => (deriv_normal_slice (hV.differentiable (by simp)) y r).symm)

private theorem sum_erase_zero_eq_succ (f : I (n + 1) → ℝ) :
    (∑ i ∈ Finset.univ.erase 0, f i) = ∑ i : I n, f i.succ := by
  have H := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : I (n + 1)))
  rw [Fin.sum_univ_succ] at H
  linarith

/-- The signed split operator used by the finite layers is the negative
metric Laplacian, applied separately to the real and imaginary components. -/
theorem complexSplitOperator_eq_neg_laplace {O : Set Z} (hO : IsOpen O)
    {g : MetricField (n + 1)} (hg : CalderonN.SmoothMetric O g)
    (hNorm : HasNormalMetricBlock 0 g O) {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V)
    (y : Y) (t : ℝ) (hz : signedLayerCoordinates (y,t) ∈ O) :
    let z := signedLayerCoordinates (y,t)
    complexSplitOperator (Matrix.of (fun i j : I n => (((g z)⁻¹ i.succ j.succ : ℝ) : ℂ)))
      ((-2 * laplaceFirstCoeff g z 0 : ℝ) : ℂ)
      (fun i : I n => (laplaceFirstCoeff g z i.succ : ℂ)) V y t =
      ⟨-laplace g (Complex.reCLM ∘ V ∘ signedLayerCoordinates.symm) z,
        -laplace g (Complex.imCLM ∘ V ∘ signedLayerCoordinates.symm) z⟩ := by
  let z := signedLayerCoordinates (y,t)
  have hN := laplace_normal_firstCoeff hO hg hNorm hz
  have hL (R : ℂ →L[ℝ] ℝ) :
      laplace g (R ∘ V ∘ signedLayerCoordinates.symm) z =
        R (splitNormalSecond V y t) + laplaceFirstCoeff g z 0 * R (splitNormal V y t) +
          ((∑ i : I n, ∑ j : I n, (g z)⁻¹ i.succ j.succ * R (splitSecond V y t i j)) +
            ∑ i : I n, laplaceFirstCoeff g z i.succ * R (splitFirst V y t i)) := by
    rw [laplace_eq_normal_split hO hg hNorm hz, ← hN, tangentialLaplace]
    simp_rw [sum_erase_zero_eq_succ]
    simp only [z,coordDeriv_read_signed_first hV,coordDeriv_read_signed_second hV,
      coordDeriv_read_signed_normal hV,coordDeriv_read_signed_normalSecond hV]
  change complexSplitOperator
    (Matrix.of (fun i j : I n => (((g z)⁻¹ i.succ j.succ : ℝ) : ℂ)))
    ((-2 * laplaceFirstCoeff g z 0 : ℝ) : ℂ) (fun i => (laplaceFirstCoeff g z i.succ : ℂ)) V y t =
    ⟨-laplace g (Complex.reCLM ∘ V ∘ signedLayerCoordinates.symm) z,
      -laplace g (Complex.imCLM ∘ V ∘ signedLayerCoordinates.symm) z⟩
  have hτ : ((-2 * laplaceFirstCoeff g z 0 : ℝ) : ℂ) / 2 = ((-laplaceFirstCoeff g z 0 : ℝ) : ℂ) := by
    have hReal : (-2 : ℝ) * laplaceFirstCoeff g z 0 / 2 = -laplaceFirstCoeff g z 0 := by ring
    exact_mod_cast hReal
  unfold complexSplitOperator
  rw [hτ]
  apply Complex.ext
  · simp [hL Complex.reCLM,Complex.re_sum,Complex.mul_re]
    ring
  · simp [hL Complex.imCLM,Complex.im_sum,Complex.mul_im]
    ring

end CalderonPatch.BoundaryLayer
