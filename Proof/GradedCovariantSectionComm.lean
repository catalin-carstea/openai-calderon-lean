import Proof.Curvature

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres

variable {E₂ E₁ E₀ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]

def gradedSectionCovariantDerivative (J : E₁ →L[ℝ] E₀)
    (A : X → X → E₁ →L[ℝ] E₀) (U : X → E₁) (y a : X) : E₀ :=
  J (fderiv ℝ U y a)-A y a (U y)

/-- A genuine two-grade covariant commutator. The compatibility equations
are explicit maps between the grades; no underlying carrier identification
is used. -/
theorem gradedSectionCovariantDerivative_commutator
    (I₂₁ : E₂ →L[ℝ] E₁) (I₁₀ : E₁ →L[ℝ] E₀)
    (A : X → X → E₁ →L[ℝ] E₀) (B : X → X → E₂ →L[ℝ] E₁)
    (U : X → E₂) (y a b : X) (hU : ContDiffAt ℝ ∞ U y)
    (hBa : DifferentiableAt ℝ (fun x => B x a) y)
    (hBb : DifferentiableAt ℝ (fun x => B x b) y)
    (hCompatA : I₁₀.comp (B y a)=(A y a).comp I₂₁)
    (hCompatB : I₁₀.comp (B y b)=(A y b).comp I₂₁) :
    gradedSectionCovariantDerivative I₁₀ A
        (fun x => gradedSectionCovariantDerivative I₂₁ B U x b) y a-
      gradedSectionCovariantDerivative I₁₀ A
        (fun x => gradedSectionCovariantDerivative I₂₁ B U x a) y b=
    -I₁₀ (fderiv ℝ (fun x => B x b) y a (U y)-
      fderiv ℝ (fun x => B x a) y b (U y))+
      A y a (B y b (U y))-A y b (B y a (U y)) := by
  have hDU := (hU.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hUD := hU.differentiableAt (by simp)
  have hFixed (c : X) : HasFDerivAt (fun x => fderiv ℝ U x c)
      ((ContinuousLinearMap.apply ℝ E₂ c).comp (fderiv ℝ (fderiv ℝ U) y)) y :=
    (ContinuousLinearMap.apply ℝ E₂ c).hasFDerivAt.comp y hDU.hasFDerivAt
  have hD (c v : X) (hBc : DifferentiableAt ℝ (fun x => B x c) y) :
      fderiv ℝ (fun x => gradedSectionCovariantDerivative I₂₁ B U x c) y v=
        I₂₁ (fderiv ℝ (fderiv ℝ U) y v c)-
          (B y c (fderiv ℝ U y v)+fderiv ℝ (fun x => B x c) y v (U y)) := by
    have hh := (I₂₁.hasFDerivAt.comp y (hFixed c)).sub
      (hBc.hasFDerivAt.clm_apply hUD.hasFDerivAt)
    change HasFDerivAt (fun x => gradedSectionCovariantDerivative I₂₁ B U x c) _ y at hh
    simpa only [_root_.sub_apply,_root_.add_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.flip_apply] using DFunLike.congr_fun hh.fderiv v
  have hCa (u : E₂) : I₁₀ (B y a u)=A y a (I₂₁ u) := DFunLike.congr_fun hCompatA u
  have hCb (u : E₂) : I₁₀ (B y b u)=A y b (I₂₁ u) := DFunLike.congr_fun hCompatB u
  change (I₁₀ (fderiv ℝ (fun x => gradedSectionCovariantDerivative I₂₁ B U x b) y a)-
      A y a (gradedSectionCovariantDerivative I₂₁ B U y b))-
    (I₁₀ (fderiv ℝ (fun x => gradedSectionCovariantDerivative I₂₁ B U x a) y b)-
      A y b (gradedSectionCovariantDerivative I₂₁ B U y a))= _
  rw [hD b a hBb,hD a b hBa]
  simp only [gradedSectionCovariantDerivative,
    map_sub,map_add,hCa,hCb,(hU.isSymmSndFDerivAt (by simp)).eq a b]
  abel

end ShrinkingSpheres
