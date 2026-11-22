module

public import Proof.CalderonN.MovingTracePerturbationBaseNormal
public import Proof.CalderonN.TraceCoordinatePotential

import Mathlib.Tactic

/-! Coordinate normal form of the perturbation in the physical trace. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem actualSupportedMovingTrace_perturbation_base_normal
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
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    let B (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
    let K₀ := supportedCoordinateModelPotential hY hg hK he hA hEll S hlog
    let K₁ := supportedCoordinateModelPotentialDerivative hY hg hK he hA hEll S hlog
    movingTracePerturbation a (a-g) b V D E F₁ =
      (∑ i,∑ j,a i j*(B i*B j))+
        (∑ i,movingTraceFirstBaseCoeff a (a-g) b V K₀ E F₁ i*B i)+
        movingTraceZeroBaseCoeff a (a-g) b V K₀ E F₁ K₁ := by
  dsimp only
  rw [show supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S =
      (fun i : I dim => smoothSupportedTraceBaseDiff (Y:=Y) (axis i)) +
        supportedCoordinateModelPotential hY hg hK he hA hEll S hlog from
    funext (supportedCoordinateModelDerivative_eq_base_add_potential hY hg hK he hA hEll S hlog)]
  exact movingTracePerturbation_base_normal _ _ _ _ _ _ _ _ _
    (supportedCoordinateModelPotential_comm_base hY hg hK he hA hEll S hlog hn)

end CalderonN
