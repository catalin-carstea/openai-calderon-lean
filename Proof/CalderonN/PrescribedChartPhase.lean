module

public import Proof.CalderonN.ChartBilinear
public import Proof.CalderonN.CovariantHessian

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

@[expose] public section

/-! The phase polynomial adopts the quadratic derivative calculation in
`StrictWeightPrescribedMetricJets` at anisotropic-calderon-lean revision
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

noncomputable section
open Set Matrix
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ}

/-- Prescribe a first derivative and covariant Hessian in the same chart. -/
theorem exists_phase_of_jets {g : (MetricField dim)} (hg : SmoothMetric univ g) (p : (X dim))
    (ell : (X dim) →L[ℝ] ℝ) (P : selfAdjoint (Mat dim)) :
    ∃ θ : (X dim) → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ fderiv ℝ θ p = ell ∧
      (∀ v w : (X dim), fderiv ℝ (fderiv ℝ θ) p v w =
        chartBilinear (P : (Mat dim)) v w + ell (connection g p v w)) ∧
      ∀ i j : (I dim), metricHessian g θ p i j = (P : (Mat dim)) i j := by
  let M : (Mat dim) := fun i j => ∑ k, ell (axis k) * christoffel g p k i j
  let B := chartBilinear (P : (Mat dim)) + chartBilinear M
  have hMs : M.IsHermitian := by
    ext i j
    change (∑ k, ell (axis k) * christoffel g p k j i) =
      ∑ k, ell (axis k) * christoffel g p k i j
    exact Finset.sum_congr rfl fun k _ => by rw [christoffel_symm_of_smoothMetric hg p k j i]
  have hP : (P : (Mat dim)).IsHermitian := P.2
  have hBsym (v w : (X dim)) : B v w = B w v := by
    change chartBilinear (P : (Mat dim)) v w + chartBilinear M v w =
      chartBilinear (P : (Mat dim)) w v + chartBilinear M w v
    rw [chartBilinear_symm hP v w, chartBilinear_symm hMs v w]
  let theta : (X dim) → ℝ := fun x => ell (x-p) + (1/2 : ℝ) * B (x-p) (x-p)
  have hTrans : ContDiff ℝ ∞ (fun x : (X dim) => x-p) := contDiff_id.sub contDiff_const
  have hSmooth : ContDiff ℝ ∞ theta :=
    (ell.contDiff.comp hTrans).add
      (contDiff_const.mul ((B.contDiff.comp hTrans).clm_apply hTrans))
  have hDeriv (x : (X dim)) : HasFDerivAt theta (ell + B (x-p)) x := by
    have hT : HasFDerivAt (fun y : (X dim) => y-p) (ContinuousLinearMap.id ℝ (X dim)) x :=
      (hasFDerivAt_id x).sub_const p
    have hEll : HasFDerivAt (fun y : (X dim) => ell (y-p)) ell x := by
      have hOuter : HasFDerivAt (fun v : (X dim) => ell v) ell (x-p) :=
        ContinuousLinearMap.hasFDerivAt ell
      have hComp := HasFDerivAt.comp (f := fun y : (X dim) => y-p)
        (f' := ContinuousLinearMap.id ℝ (X dim)) (g := fun v : (X dim) => ell v) (g' := ell)
        x hOuter hT
      simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hComp
    have hQuad := B.hasFDerivAt_of_bilinear hT hT
    have hA : (1/2 : ℝ) •
        (B.precompR (X dim) (x-p) (ContinuousLinearMap.id ℝ (X dim)) +
          B.precompL (X dim) (ContinuousLinearMap.id ℝ (X dim)) (x-p)) = B (x-p) := by
      apply ContinuousLinearMap.ext
      intro v
      change (1/2 : ℝ) * (B (x-p) v + B v (x-p)) = B (x-p) v
      rw [hBsym v (x-p)]
      ring
    have h := hEll.add (hQuad.const_smul (1/2 : ℝ))
    rw [hA] at h
    have hFunction : ((fun y : (X dim) => ell (y-p)) +
        (1/2 : ℝ) • (fun y : (X dim) => B (y-p) (y-p))) = theta := by
      funext y
      rfl
    rw [hFunction] at h
    exact h
  have hDf : fderiv ℝ theta = (fun x : (X dim) => ell + B (x-p)) :=
    funext (fun x => (hDeriv x).fderiv)
  have hFirst : fderiv ℝ theta p = ell := by
    rw [hDf]
    simp only [sub_self,map_zero,add_zero]
  have hSecond : fderiv ℝ (fderiv ℝ theta) p = B := by
    rw [hDf]
    have hT : HasFDerivAt (fun x : (X dim) => x-p) (ContinuousLinearMap.id ℝ (X dim)) p :=
      (hasFDerivAt_id p).sub_const p
    have hOuter : HasFDerivAt (fun v : (X dim) => B v) B (p-p) :=
      ContinuousLinearMap.hasFDerivAt B
    have hComp := HasFDerivAt.comp (f := fun x : (X dim) => x-p)
      (f' := ContinuousLinearMap.id ℝ (X dim)) (g := fun v : (X dim) => B v) (g' := B)
      p hOuter hT
    have hBderiv : HasFDerivAt (fun x : (X dim) => B (x-p)) B p := by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hComp
    exact (hBderiv.const_add ell).fderiv
  refine ⟨theta,hSmooth,by simp [theta],hFirst,?_,?_⟩
  · intro v w
    rw [hSecond]
    change chartBilinear (P : (Mat dim)) v w + chartBilinear M v w = _
    rw [covector_connection_eq_bilinear g p v w ell]
  · intro i j
    let L : ((X dim) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (axis j)
    have hD : DifferentiableAt ℝ (fderiv ℝ theta) p :=
      by
        have h' := hSmooth.contDiffOn.fderiv_of_isOpen (m := ∞) isOpen_univ (by simp)
        exact (contDiffOn_univ.mp h').differentiable (by simp) p
    have h := L.hasFDerivAt.comp p hD.hasFDerivAt
    have he : hessian theta p i j = B (axis i) (axis j) := by
      change fderiv ℝ (L ∘ fderiv ℝ theta) p (axis i) = _
      rw [h.fderiv]
      change fderiv ℝ (fderiv ℝ theta) p (axis i) (axis j) = _
      rw [hSecond]
    unfold metricHessian
    rw [he]
    change chartBilinear (P : (Mat dim)) (axis i) (axis j) + chartBilinear M (axis i) (axis j) -
      (∑ k, christoffel g p k i j * fderiv ℝ theta p (axis k)) = _
    rw [chartBilinear_axis, chartBilinear_axis, hFirst]
    simp only [M, mul_comm]
    ring

end CalderonN
