module

public import Proof.CalderonN.MovingTracePrincipalDecomposition
public import Proof.CalderonN.MovingTraceCoordinateSquare
public import Proof.CalderonN.ActualSupportedGaussExpansion

import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! Assemble the exact moving trace decomposition on the physical core.
The perturbation and lower-order term use the actual Gauss coefficients. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

section Algebra
variable {R ι : Type*} [Ring R] [Fintype ι]

@[expose] def movingTracePerturbation (a h : ι → ι → R) (b V D E F : ι → R) : R :=
  let W := E+F
  (∑ i,∑ j,h i j*(V i*V j+V i*D j+V j*D i))+
    (∑ i,∑ j,a i j*(V i*E j+E i*V j+
      (D i*D j+W j*D i+W i*D j+W i*W j)))+
    ∑ i,b i*(D i+W i)

@[expose] def movingTraceLowerOrder (a : ι → ι → R) (b V D E F : ι → R) : R :=
  let W := E+F
  (∑ i,∑ j,a i j*((D i*V j-V j*D i)+(V i*F j+F i*V j)+(D i*W j-W j*D i)))+
    ∑ i,b i*V i

theorem movingTrace_square_eq_model_add (a g : ι → ι → R) (b V D E F : ι → R) (T : R)
    (hg : ∀ i j,g i j = g j i)
    (hVV : (∑ i,∑ j,g i j*(V i*V j)) = 0)
    (hT : (∑ i,∑ j,g i j*(V i*D j)) = T) :
    (∑ i,∑ j,a i j*((V i+D i+E i+F i)*(V j+D j+E j+F j)))+
      (∑ i,b i*(V i+D i+E i+F i)) =
      T+T+movingTracePerturbation a (a-g) b V D E F+movingTraceLowerOrder a b V D E F := by
  have h := movingTrace_principal_decomposition g (a-g) b V D E F hg hVV
  dsimp only at h
  have hEq : g+(a-g) = a := by abel
  rw [hEq,hT] at h
  exact h

end Algebra

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem supportedReferenceTraceCoeff_symm (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ)
    (hK : 0 < K) (hr : ContDiffOn ℝ ∞ d.radius Y) (i j : I dim) :
    supportedReferenceTraceCoeff hY hg hK hr i j = supportedReferenceTraceCoeff hY hg hK hr j i := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  simp only [supportedReferenceTraceCoeff,smoothSupportedTraceBaseMul_fiber]
  have hSym : (d.γ x)⁻¹ i j = (d.γ x)⁻¹ j i :=
    congrFun (congrFun (hg.posDef hK hx).inv.isHermitian.isSymm.eq j) i
  rw [hSym]

theorem actualSupportedMovingTrace_decompose
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i=j then 1 else 0)
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
    let T := physicalRaisingModel hY hg hK he hlog hA hEll S
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    let U := movingTracePerturbation a (a-g) b V D E F₁
    let J := movingTraceLowerOrder a b V D E F₁
    supportedMovingTrace hY hg hK he (actualGaussFiberFamily F) hC hr hQ hb =
      (2:ℝ) • T+U+J := by
  dsimp only
  rw [supportedMovingTrace_eq_coordinateSquare hY hg hK he hr hQ hb]
  simp_rw [actualSupportedTraceDerivative_expand hY hg hK he hr hr₀ hlog hA hEll S F hC hF]
  have hT := supportedCoordinateRaising_cross_eq_model hY hg hK he hlog hA hEll S hframe hr hr₀
  have hVV := supportedReferenceVelocity_square_zero hY hg hK he hr hr₀ hA hEll S hn hframe
  have hEq := movingTrace_square_eq_model_add
    (supportedPrincipalTraceCoeff hY hr hQ) (supportedReferenceTraceCoeff hY hg hK hr)
    (supportedCoordinateTraceDrift hY hg hK hr hQ hb)
    (supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S)
    (supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S)
    (actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF)
    (actualSupportedAffine hY F hF)
    (physicalRaisingModel hY hg hK he hlog hA hEll S) (supportedReferenceTraceCoeff_symm hY hg hK hr) hVV hT
  rw [two_smul]
  exact hEq

end CalderonN
