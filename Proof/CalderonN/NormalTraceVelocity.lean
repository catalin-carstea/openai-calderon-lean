module

public import Proof.CalderonN.NormalizedBallMetric

import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! Adapted from `NormalTraceVelocity` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Matrix
open scoped ContDiff Matrix Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Radius times the moving physical boundary velocity in fixed-ball
coordinates. The independent parameter `b` is the derivative of the
radius along the specified base direction. -/
@[expose] def scaledNormalTraceVelocity (γ : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (y : (X dim)) (s b : ℝ) (z a : (X dim)) : (X dim) :=
  let w := frameVector e y z
  let D := coordinateMatrix (normalizedBallDerivative E e y s z)
  let v := fderiv ℝ E (y,s • w) (a,b • w - s • connection γ y a w)
  WithLp.toLp 2 (D⁻¹ *ᵥ fun i => v i)

theorem normalizedBallDerivative_scaledNormalTraceVelocity
    (γ : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (y : (X dim)) (s b : ℝ) (z a : (X dim))
    (hD : (coordinateMatrix (normalizedBallDerivative E e y s z)).det ≠ 0) :
    normalizedBallDerivative E e y s z (scaledNormalTraceVelocity γ E e y s b z a) =
      fderiv ℝ E (y,s • frameVector e y z)
        (a,b • frameVector e y z - s • connection γ y a (frameVector e y z)) := by
  let D := coordinateMatrix (normalizedBallDerivative E e y s z)
  let v := fderiv ℝ E (y,s • frameVector e y z)
    (a,b • frameVector e y z - s • connection γ y a (frameVector e y z))
  have h := coordinateMatrix_mulVec (normalizedBallDerivative E e y s z)
    (scaledNormalTraceVelocity γ E e y s b z a)
  have heq : D *ᵥ (D⁻¹ *ᵥ fun i => v i) = fun i => v i := by
    rw [mulVec_mulVec,Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.mpr hD),one_mulVec]
  ext i
  exact (congrFun h i).symm.trans (congrFun heq i)

theorem fderiv_normalBallChartMap_eq_radius_smul {E : (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ E) (e : (Frame dim)) (y : (X dim)) (s : ℝ) (z : (X dim)) :
    fderiv ℝ (normalBallChartMap E e y s) z = s • normalizedBallDerivative E e y s z := by
  rw [normalBallChartMap_deriv hE]
  apply ContinuousLinearMap.ext
  intro a
  simp only [normalizedBallDerivative,ContinuousLinearMap.comp_apply,_root_.smul_apply,map_smul]

theorem hasFDerivAt_normalBallChartMap_radius_smul_of_differentiableAt
    {E : X dim × X dim → X dim} (e : Frame dim) (y : X dim) (r : ℝ) (z : X dim)
    (hE : DifferentiableAt ℝ E (y,r • frameVector e y z)) :
    HasFDerivAt (normalBallChartMap E e y r) (r • normalizedBallDerivative E e y r z) z := by
  let T := frameVectorL (e y)
  let V := r • T
  have hV (z : X dim) : V z = r • frameVector e y z := by
    change r • T z = _
    rw [show T z = frameVectorL (e y) z from rfl,frameVectorL_apply_frame]
  have hE' : HasFDerivAt E (fderiv ℝ E (y,V z)) (y,V z) := by
    rw [hV]
    exact hE.hasFDerivAt
  have hD : HasFDerivAt (fun x => E (y,x))
      ((fderiv ℝ E (y,V z)).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim))) (V z) :=
    hE'.comp (V z) (hasFDerivAt_prodMk_right y (V z))
  have h := hD.comp z V.hasFDerivAt
  have hF : normalBallChartMap E e y r = (fun x => E (y,x)) ∘ V := by
    funext x
    change E (y,r • frameVector e y x) = E (y,V x)
    rw [hV]
  rw [hF]
  have hD' := hD.fderiv
  have hScale : r • normalizedBallDerivative E e y r z =
      (((fderiv ℝ E (y,V z)).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim))).comp V) := by
    rw [normalizedBallDerivative,← hV z,hD',show V = r • T from rfl,ContinuousLinearMap.comp_smul]
  exact h.congr_fderiv hScale.symm

theorem fderiv_scaledNormalTraceVelocity_of_differentiableAt
    {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)}
    (e : (Frame dim)) {r : (X dim) → ℝ} {y z : (X dim)}
    (hE : DifferentiableAt ℝ E (y,r y • frameVector e y z)) (hr : DifferentiableAt ℝ r y)
    {u : (X dim) → ℝ} (hu : DifferentiableAt ℝ u (normalBallChartMap E e y (r y) z)) (a : (X dim))
    (hD : (coordinateMatrix (normalizedBallDerivative E e y (r y) z)).det ≠ 0) :
    fderiv ℝ (u ∘ normalBallChartMap E e y (r y)) z
      (scaledNormalTraceVelocity γ E e y (r y) (fderiv ℝ r y a) z a) =
      r y * horizontal γ (fun q => u (endpoint E r q)) y (frameVector e y z) a := by
  let w := frameVector e y z
  let b := fderiv ℝ r y a
  let V := scaledNormalTraceVelocity γ E e y (r y) b z a
  have hDer := hasFDerivAt_normalBallChartMap_radius_smul_of_differentiableAt e y (r y) z hE
  have hF := (hu.hasFDerivAt.comp z hDer).fderiv
  change fderiv ℝ (u ∘ normalBallChartMap E e y (r y)) z V = _
  rw [hF,ContinuousLinearMap.comp_apply,
    _root_.smul_apply,map_smul,smul_eq_mul,normalizedBallDerivative_scaledNormalTraceVelocity γ E e y
      (r y) b z a hD]
  congr 1
  let p := (y,w)
  let R (q : (X dim) × (X dim)) := (q.1,r q.1 • q.2)
  have hR₁ : HasFDerivAt (fun q : (X dim) × (X dim) => r q.1)
      ((fderiv ℝ r y).comp (ContinuousLinearMap.fst ℝ (X dim) (X dim))) p :=
    hr.hasFDerivAt.comp p hasFDerivAt_fst
  have hR := hasFDerivAt_fst.prodMk (hR₁.smul (hasFDerivAt_snd (p := p)))
  have hD₁ := hE.hasFDerivAt.comp p hR
  have hU := hu.hasFDerivAt.comp p hD₁
  change (fderiv ℝ u (normalBallChartMap E e y (r y) z))
    ((fderiv ℝ E (R p)) (a,b • w-r y • connection γ y a w)) =
      fderiv ℝ (u ∘ E ∘ R) p (a,-connection γ y a w)
  have hUEq := hU.fderiv
  change fderiv ℝ (u ∘ E ∘ R) p = _ at hUEq
  rw [hUEq]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smulRight_apply,_root_.add_apply,_root_.smul_apply]
  congr 3
  change _ = r y • -connection γ y a w + b • w
  rw [smul_neg,sub_eq_add_neg,add_comm]

/-- The fixed-ball derivative in the scaled velocity is the physical
horizontal derivative multiplied by exactly one power of the radius. -/
theorem fderiv_scaledNormalTraceVelocity
    {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (e : (Frame dim)) {r : (X dim) → ℝ} {y z : (X dim)} (hr : DifferentiableAt ℝ r y)
    {u : (X dim) → ℝ} (hu : DifferentiableAt ℝ u (normalBallChartMap E e y (r y) z)) (a : (X dim))
    (hD : (coordinateMatrix (normalizedBallDerivative E e y (r y) z)).det ≠ 0) :
    fderiv ℝ (u ∘ normalBallChartMap E e y (r y)) z
      (scaledNormalTraceVelocity γ E e y (r y) (fderiv ℝ r y a) z a) =
      r y * horizontal γ (fun q => u (endpoint E r q)) y (frameVector e y z) a :=
  fderiv_scaledNormalTraceVelocity_of_differentiableAt e (hE.differentiable (by simp) _) hr hu a hD

end CalderonN
