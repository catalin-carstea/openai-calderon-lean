module

public import Proof.CalderonN.MovingTracePerturbationAdjoint
public import Proof.CalderonN.SupportedTraceModelFactorAdjoints
public import Proof.CalderonN.ActualAffinePairedAdjoint

import Proof.CalderonN.MetricConnection
import Mathlib.Tactic

/-! The perturbation of the actual moving trace has a genuine paired
adjoint on the compactly supported trace space. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem exists_pairedAdjoint_actualMovingTracePerturbation_of_paired_drift
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i)) 
    (hDensity : ContDiffOn ℝ ∞ (firstDensityCenterLinear d) Y)
    (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y) (hμ₀ : ∀ x ∈ Y,0 < μ x)
    (b : I dim → Module.End ℝ (SmoothSupportedTraceSection Y))
    (hb' : ∀ i,PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) (b i) (b i))
    (hAdj : ∀ i,∃ C',PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (smoothSupportedTraceFiberAction hY (actualGaussFiberFamily F i) (hC i)) C') :
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    ∃ U',PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (movingTracePerturbation a (a-g) b V D E F₁) U' := by
  dsimp only
  let Pair := smoothSupportedTracePairingL hn hY μ hμ
  let a := supportedPrincipalTraceCoeff hY hr hQ
  let g := supportedReferenceTraceCoeff hY hg hK hr
  let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
  let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
  let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
  let F₁ := actualSupportedAffine hY F hF
  have ha (i j : I dim) : PairedAdjoint Pair (a i j) (a i j) := pairedAdjoint_supportedBaseMul hn hY μ hμ _ _
  have hg' (i j : I dim) : PairedAdjoint Pair (g i j) (g i j) :=
    pairedAdjoint_supportedBaseMul hn hY μ hμ _ _
  have hV (i : I dim) : ∃ V',PairedAdjoint Pair (V i) V' :=
    ⟨_,pairedAdjoint_supportedLeadingTraceVelocity hn hY hg he μ hμ hA hEll S hr hr₀ i⟩
  have hD (i : I dim) : ∃ D',PairedAdjoint Pair (D i) D' :=
    ⟨_,pairedAdjoint_supportedCoordinateModelDerivative hn hY hg hK he μ hμ hA hEll S hμ₀ hlog i⟩
  have hF' (i : I dim) : ∃ F',PairedAdjoint Pair (F₁ i) F' :=
    exists_pairedAdjoint_actualSupportedAffine hn hY hg he hr hDensity μ hμ hA hEll S F hF i
  choose C' hC' using hAdj
  choose V' hV' using hV
  choose D' hD' using hD
  choose Q hQ' using hF'
  let B := supportedFlatDegree hA hEll S hY
  let L (i : I dim) := smoothSupportedTraceBaseMul hY (traceCoordinateLogGradient d.radius i)
    (contDiffOn_traceCoordinateLogGradient hY hlog i)
  have hB : PairedAdjoint Pair B B := pairedAdjoint_supportedFlatDegree hn hY μ hμ hA hEll S
  have hL (i : I dim) : PairedAdjoint Pair (L i) (L i) := pairedAdjoint_supportedBaseMul hn hY μ hμ _ _
  let E' (i : I dim) := C' i-V' i-B*L i-Q i
  have hE (i : I dim) : PairedAdjoint Pair (E i) (E' i) :=
    (((hC' i).sub (hV' i)).sub ((hL i).mul hB)).sub (hQ' i)
  exact ⟨_,pairedAdjoint_movingTracePerturbation Pair a (a-g) b V D E F₁ V' D' E' Q
    ha (fun i j => (ha i j).sub (hg' i j)) hb' hV' hD' hE hQ'⟩


theorem exists_pairedAdjoint_actualMovingTracePerturbation
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
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i)) 
    (hDensity : ContDiffOn ℝ ∞ (firstDensityCenterLinear d) Y)
    (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y) (hμ₀ : ∀ x ∈ Y,0 < μ x)
    (hAdj : ∀ i,∃ C',PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (smoothSupportedTraceFiberAction hY (actualGaussFiberFamily F i) (hC i)) C') :
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    ∃ U',PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (movingTracePerturbation a (a-g) b V D E F₁) U' := by
  dsimp only
  let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
  exact exists_pairedAdjoint_actualMovingTracePerturbation_of_paired_drift hn hY hg hK he hr hr₀ hlog hQ
    hA hEll S F hC hF hDensity μ hμ hμ₀ b
    (fun _ => pairedAdjoint_supportedBaseMul hn hY μ hμ _ _) hAdj

end CalderonN
