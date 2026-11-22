module

public import Proof.CalderonN.PhysicalTraceComparison
public import Proof.CalderonN.ActualSupportedTraceNorm
public import Proof.CalderonN.ActualMovingTracePairedAdjoint

import Proof.CalderonN.MetricConnection
public import Proof.CalderonN.MovingTraceDriftSplit
import Mathlib.Tactic

/-! The conditional comparison now takes the two bounds for the
exact perturbation and lower-order part of the protected trace. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem actualSupportedMovingTrace_comparison
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i=j then 1 else 0)
    (hAdj : IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius d.adjoint)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
    (hb : ∀ k,ContDiffOn ℝ ∞ (fun x => drift d.γ d.g₂ x k) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))
    (hMR : ∀ i,MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i (actualGaussFiberFamily F i) Complex.reCLM)
    (hMI : ∀ i,MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i (actualGaussFiberFamily F i) Complex.imCLM)
    {v : Field dim} (hv : smoothNear v (bundle Y d.γ))
    (H : HarmonicTestExpansion Y d.γ d.frame v) (M : AngularModelData H d.radius)
    (Ud : Module.End ℝ (SmoothSupportedTraceSection Y)) (Cerr Cj : ℝ) :
    let T := physicalRaisingModel hY hg hK he hlog hA hEll S
    let L := physicalLoweringModel hY hg hK he hlog hA hEll S
    let Td := L-physicalTraceModelCorrection hY he hA hEll S hlog
    let B := smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hg.contDiffOn_density hK)
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    let U := movingTracePerturbation a (a-g) b V D E F₁
    let J := movingTraceLowerOrder a b V D E F₁
    let u := H.traceComponent Complex.reCLM
    let w := H.traceComponent Complex.imCLM
    PairedAdjoint B U Ud →
      |movingTraceAdjointErrorForm B T Td L U Ud u+movingTraceAdjointErrorForm B T Td L U Ud w| ≤ Cerr →
      Real.sqrt (B (J u) (J u)+B (J w) (J w)) ≤ Cj →
      ∃ c : ℝ, 0 ≤ c ∧ 4*(M.raisingSquare-M.loweringSquare) ≤ c^2+Cerr ∧
        c ≤ traceNorm Y d v+Cj := by
  dsimp only
  intro hU hError hJ
  let P := supportedMovingTrace hY hg hK he (actualGaussFiberFamily F) hC hr hQ hb
  have hP := actualSupportedMovingTrace_decompose hn hY hg hK he hframe hr hr₀ hlog hQ hb
    hA hEll S F hC hF
  have hNorm := supportedMovingTrace_traceNorm hn hY hg hK he hframe hAdj
    (actualGaussFiberFamily F) hC hr hQ hb hMR hMI hv H
  exact physicalTrace_comparison_of_error_estimates hn hY hK hg he hframe hlog hA hEll S hv H M
    P _ Ud _ Cerr Cj hP hNorm hU hError hJ


theorem actualSupportedMovingTrace_comparison_drift_split
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i=j then 1 else 0)
    (hAdj : IsMovingTraceAdjoint Y d.γ d.g₁ d.frame d.expMap d.radius d.adjoint)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
    (hb : ∀ k,ContDiffOn ℝ ∞ (fun x => drift d.γ d.g₂ x k) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))
    (hMR : ∀ i,MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i (actualGaussFiberFamily F i) Complex.reCLM)
    (hMI : ∀ i,MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i (actualGaussFiberFamily F i) Complex.imCLM)
    {v : Field dim} (hv : smoothNear v (bundle Y d.γ))
    (H : HarmonicTestExpansion Y d.γ d.frame v) (M : AngularModelData H d.radius)
    (Ud : Module.End ℝ (SmoothSupportedTraceSection Y)) (Cerr Cj : ℝ) :
    let T := physicalRaisingModel hY hg hK he hlog hA hEll S
    let L := physicalLoweringModel hY hg hK he hlog hA hEll S
    let Td := L-physicalTraceModelCorrection hY he hA hEll S hlog
    let B := smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hg.contDiffOn_density hK)
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    let U := movingTracePerturbation a (a-g) 0 V D E F₁
    let J := movingTraceLowerOrder a b V D E F₁+movingTraceDriftRemainder b D E F₁
    let u := H.traceComponent Complex.reCLM
    let w := H.traceComponent Complex.imCLM
    PairedAdjoint B U Ud →
      |movingTraceAdjointErrorForm B T Td L U Ud u+movingTraceAdjointErrorForm B T Td L U Ud w| ≤ Cerr →
      Real.sqrt (B (J u) (J u)+B (J w) (J w)) ≤ Cj →
      ∃ c : ℝ, 0 ≤ c ∧ 4*(M.raisingSquare-M.loweringSquare) ≤ c^2+Cerr ∧
        c ≤ traceNorm Y d v+Cj := by
  dsimp only
  intro hU hError hJ
  let P := supportedMovingTrace hY hg hK he (actualGaussFiberFamily F) hC hr hQ hb
  have hP := actualSupportedMovingTrace_decompose hn hY hg hK he hframe hr hr₀ hlog hQ hb
    hA hEll S F hC hF
  dsimp only at hP
  rw [movingTracePerturbation_split_drift] at hP
  let a := supportedPrincipalTraceCoeff hY hr hQ
  let g := supportedReferenceTraceCoeff hY hg hK hr
  let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
  let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
  let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
  let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
  let F₁ := actualSupportedAffine hY F hF
  let U := movingTracePerturbation a (a-g) 0 V D E F₁
  let J₀ := movingTraceLowerOrder a b V D E F₁
  let Jd := movingTraceDriftRemainder b D E F₁
  let T := physicalRaisingModel hY hg hK he hlog hA hEll S
  have hP' : P = (2:ℝ) • T+U+(J₀+Jd) := by
    have h := hP
    change P = (2:ℝ) • T+(U+Jd)+J₀ at h
    rw [h]
    abel
  have hNorm := supportedMovingTrace_traceNorm hn hY hg hK he hframe hAdj
    (actualGaussFiberFamily F) hC hr hQ hb hMR hMI hv H
  exact physicalTrace_comparison_of_error_estimates hn hY hK hg he hframe hlog hA hEll S hv H M
    P _ Ud _ Cerr Cj hP' hNorm hU hError hJ

end CalderonN
