module

public import Proof.CalderonN.TraceCoordinateModel
public import Proof.CalderonN.SmoothSupportedHorizontalAdjoint

import Mathlib.Tactic

/-! The ordinary model derivative and the scaled raising factor have
their adjoints on the supported section space. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2900000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim} {r : X dim → ℝ}
variable (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
  (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

theorem pairedAdjoint_supportedLeadingTraceVelocity
    (hr : ContDiffOn ℝ ∞ r Y) (hr₀ : ∀ x ∈ Y,r x ≠ 0) (i : I dim) :
    let L := smoothSupportedTraceBaseMul hY (fun x => (r x)⁻¹) (hr.inv hr₀)
    let F (a : I dim) := smoothSupportedTraceBaseMul hY (traceFrameCoordinate g e a i)
      (contDiffOn_traceFrameCoordinate hg he a i)
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S i)
      ((∑ a : I dim,supportedLowering hA hEll S hY a*F a)*L) := by
  unfold supportedLeadingTraceVelocity supportedCoordinateRaising
  dsimp only
  exact (pairedAdjoint_supportedBaseMul hn hY μ hμ _ _).mul
    (PairedAdjoint.sum Finset.univ _ _ (fun a _ =>
      (pairedAdjoint_supportedBaseMul hn hY μ hμ _ _).mul
        (pairedAdjoint_supportedRaising hn hY μ hμ hA hEll S a)))

theorem pairedAdjoint_supportedCoordinateModelDerivative
    (hμ₀ : ∀ x ∈ Y,0 < μ x)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y) (i : I dim) :
    let H := supportedHorizontal hY hg hK he (fun _ => axis i) contDiffOn_const
    let B := supportedFlatDegree hA hEll S hY
    let D := smoothSupportedTraceBaseMul hY (traceDensityDivergence μ (fun _ => axis i))
      (contDiffOn_traceDensityDivergence hY μ hμ hμ₀ _ contDiffOn_const)
    let F := smoothSupportedTraceBaseMul hY (traceCoordinateLogGradient r i)
      (contDiffOn_traceCoordinateLogGradient hY hlog i)
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S i) (-H-D+B*F) := by
  unfold supportedCoordinateModelDerivative
  dsimp only
  exact (pairedAdjoint_supportedHorizontal hY hn μ hμ hμ₀ hg hK he _ contDiffOn_const).add
    ((pairedAdjoint_supportedBaseMul hn hY μ hμ _ _).mul
      (pairedAdjoint_supportedFlatDegree hn hY μ hμ hA hEll S))

end CalderonN
