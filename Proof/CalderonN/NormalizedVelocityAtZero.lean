module

public import Proof.CalderonN.NormalTraceVelocity

import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.NormalEndpointJets
import Mathlib.Tactic

/-! Adapted from `NormalizedVelocityAtZero` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem bijective_frameVector (γ : (MetricField dim)) (e : (Frame dim)) (y : (X dim))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0) :
    Function.Bijective (frameVector e y) := by
  let f := frameCoordinates γ y (e y)
  have hl : Function.LeftInverse f (frameVector e y) := fun v =>
    frameCoordinates_frameVector γ y v (e y) he
  have hr : Function.RightInverse f (frameVector e y) := fun v =>
    frameVector_frameCoordinates γ y v (e y) he
  exact ⟨hl.injective,hr.surjective⟩

theorem normalizedBallDerivative_det_at_zero
    {Y Ω : Set (X dim)} {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {ρ : (X dim) → ℝ}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E ρ) {y : (X dim)} (hy : y ∈ Y)
    {e : (Frame dim)} (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (z : (X dim)) : (coordinateMatrix (normalizedBallDerivative E e y 0 z)).det ≠ 0 := by
  rw [normalizedBallDerivative_zero hE hN hy he]
  have hBF : ⇑(frameVectorL (e y)) = frameVector e y := funext (frameVectorL_apply_frame e y)
  have hF : fderiv ℝ (frameVector e y) z = frameVectorL (e y) :=
    by simpa only [hBF] using (frameVectorL (e y)).fderiv (x := z)
  have hBij : Function.Bijective (fderiv ℝ (frameVector e y) z) :=
    hF.symm ▸ (by simpa only [hBF] using bijective_frameVector γ e y he)
  have h := coordinateJacobian_det_ne_zero hBij
  rw [coordinateJacobian,hF] at h
  exact h

/-- The limiting scaled normal velocity consists of translation in the
orthonormal frame and the radial velocity coming from the radius derivative. -/
theorem scaledNormalTraceVelocity_zero
    {Y Ω : Set (X dim)} (hY : IsOpen Y) {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {ρ : (X dim) → ℝ}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E ρ) {y : (X dim)} (hy : y ∈ Y)
    {e : (Frame dim)} (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (b : ℝ) (w a : (X dim)) :
    scaledNormalTraceVelocity γ E e y 0 b w a = frameCoordinates γ y (e y) a+b • w := by
  let A := fderiv ℝ E (y,(0:(X dim)))
  let B := frameVectorL (e y)
  have hE₀ : (fun x : (X dim) => E (x,0)) =ᶠ[𝓝 y] id :=
    Filter.mem_of_superset (hY.mem_nhds hy) (fun _ hx => hN.exp_zero hx)
  have hInl : HasFDerivAt (fun x : (X dim) => (x,(0:(X dim)))) (ContinuousLinearMap.inl ℝ (X dim) (X dim)) y := by
    exact hasFDerivAt_prodMk_left y 0
  have hA₁ := (((hE.differentiable (by simp) (y,0)).hasFDerivAt.comp y hInl).fderiv)
  have hAC : A (a,0) = a := by
    have h := hE₀.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (E ∘ fun x : (X dim) => (x,0)) y = fderiv ℝ id y at h
    rw [hA₁,fderiv_id] at h
    exact congrArg (fun Q : (X dim) →L[ℝ] (X dim) => Q a) h
  have hA₂ : A (0,B w) = B w := by
    have h := ((hE.differentiable (by simp) (y,0)).hasFDerivAt.comp (0:(X dim))
      (hasFDerivAt_prodMk_right y (0:(X dim)))).fderiv
    have heq := normalizedBallDerivative_zero hE hN hy he w
    rw [normalizedBallDerivative,zero_smul] at heq
    change (fderiv ℝ (E ∘ Prod.mk y) (0:(X dim))).comp B = B at heq
    rw [h] at heq
    exact congrArg (fun Q : (X dim) →L[ℝ] (X dim) => Q w) heq
  have hV := normalizedBallDerivative_scaledNormalTraceVelocity γ E e y 0 b w a
    (normalizedBallDerivative_det_at_zero hE hN hy he w)
  rw [normalizedBallDerivative_zero hE hN hy he,zero_smul,zero_smul,sub_zero] at hV
  have hBF : ⇑B = frameVector e y := funext (frameVectorL_apply_frame e y)
  have hB : Function.Injective B := hBF.symm ▸ (bijective_frameVector γ e y he).1
  apply hB
  rw [hV,map_add,map_smul]
  have hBack : B (frameCoordinates γ y (e y) a) = a := by
    rw [hBF]
    simpa only [frameVector] using frameVector_frameCoordinates γ y a (e y) he
  rw [hBack]
  rw [← frameVectorL_apply_frame]
  change A (a,b • B w) = a+b • B w
  have hSum : (a,b • B w) = (a,0)+b • ((0:(X dim)),B w) := by simp
  rw [hSum,map_add,map_smul,hAC,hA₂]

end CalderonN
