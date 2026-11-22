module

public import Proof.CalderonN.PhysicalMovingTraceDecomposition
public import Proof.CalderonN.TraceCoordinateRadialCancellation

import Mathlib.Tactic

/-! Cancel the radius inverse from each leading-velocity term of the
actual lower-order complement. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem actualSupportedMovingTrace_lowerOrder_cancel_radius
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
    (hb : ∀ k,ContDiffOn ℝ ∞ (fun x => drift d.γ d.g₂ x k) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i)) :
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    let q (i j : I dim) := smoothSupportedTraceBaseMul hY
      (fun x => principal d.γ d.g₂ x i j) (hQ i j)
    let k (i : I dim) := smoothSupportedTraceBaseMul hY (traceCoordinateDrift d.γ d.g₂ i)
      (contDiffOn_traceCoordinateDrift hY hg hK hQ hb i)
    let H := supportedCoordinateHorizontal hY hg hK he
    let R := supportedCoordinateRaising hY hg he hA hEll S
    let W := E+F₁
    movingTraceLowerOrder a b V D E F₁ =
      (∑ i,∑ j,q i j*((H i*R j-R j*H i)+(R i*F₁ j+F₁ i*R j)))+
      (∑ i,∑ j,a i j*(D i*W j-W j*D i))+(∑ i,k i*R i) := by
  dsimp only
  let a := supportedPrincipalTraceCoeff hY hr hQ
  let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
  let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
  let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
  let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
  let F₁ := actualSupportedAffine hY F hF
  let W := E+F₁
  let q (i j : I dim) := smoothSupportedTraceBaseMul hY
    (fun x => principal d.γ d.g₂ x i j) (hQ i j)
  let k (i : I dim) := smoothSupportedTraceBaseMul hY (traceCoordinateDrift d.γ d.g₂ i)
    (contDiffOn_traceCoordinateDrift hY hg hK hQ hb i)
  let H := supportedCoordinateHorizontal hY hg hK he
  let R := supportedCoordinateRaising hY hg he hA hEll S
  let I₀ := smoothSupportedTraceBaseMul hY (fun x => (d.radius x)⁻¹) (hr.inv hr₀)
  have hAq (i j : I dim) : a i j*I₀ = q i j := by
    unfold a I₀ q supportedPrincipalTraceCoeff
    rw [← smoothSupportedTraceBaseMul_mul hY]
    apply smoothSupportedTraceBaseMul_congr
    intro x hx
    exact mul_right_comm _ _ _ |>.trans (by rw [mul_inv_cancel₀ (hr₀ x hx),one_mul])
  have hBk (i : I dim) : b i*I₀ = k i := by
    unfold b I₀ k supportedCoordinateTraceDrift
    rw [← smoothSupportedTraceBaseMul_mul hY]
    apply smoothSupportedTraceBaseMul_congr
    intro x hx
    exact mul_right_comm _ _ _ |>.trans (by rw [mul_inv_cancel₀ (hr₀ x hx),one_mul])
  have hFcomm (i : I dim) : F₁ i*I₀ = I₀*F₁ i :=
    (smoothSupportedTraceBaseMul_comm_fiber hY _ _ _ _).symm
  have hDV (i j : I dim) : D i*V j-V j*D i = I₀*(H i*R j-R j*H i) :=
    supportedCoordinateModel_comm_leadingVelocity hY hg hK he hA hEll S hr hr₀ hlog hn i j
  have hV (i : I dim) : V i = I₀*R i := rfl
  have h₁ (i j : I dim) : a i j*((D i*V j-V j*D i)+(V i*F₁ j+F₁ i*V j)) =
      q i j*((H i*R j-R j*H i)+(R i*F₁ j+F₁ i*R j)) := by
    rw [hDV,hV i,hV j,← mul_assoc (F₁ i) I₀,hFcomm,mul_assoc I₀ (R i) (F₁ j),
      mul_assoc I₀ (F₁ i) (R j),← mul_add,← mul_add,← mul_assoc,hAq]
  have h₂ (i : I dim) : b i*V i = k i*R i := by rw [hV,← mul_assoc,hBk]
  change (∑ i,∑ j,a i j*((D i*V j-V j*D i)+(V i*F₁ j+F₁ i*V j)+(D i*W j-W j*D i)))+
    (∑ i,b i*V i) = _
  have hSplit (i j : I dim) : a i j*((D i*V j-V j*D i)+(V i*F₁ j+F₁ i*V j)+
      (D i*W j-W j*D i)) =
      q i j*((H i*R j-R j*H i)+(R i*F₁ j+F₁ i*R j))+a i j*(D i*W j-W j*D i) := by
    rw [mul_add,h₁]
  simp only [hSplit,h₂,Finset.sum_add_distrib]
  rfl

end CalderonN
