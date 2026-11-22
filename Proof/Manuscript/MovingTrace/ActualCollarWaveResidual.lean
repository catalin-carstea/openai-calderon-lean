module

public import Proof.Manuscript.MovingTrace.DephasedCollarResidual
public import Proof.Manuscript.MovingTrace.ScaledPhysicalCollarOperator
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000

open CalderonPaper Set Finset
open CalderonN (X I axis)
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {U : Set (P × X n)} (B : ParametricLayerCoefficients (n := n) U)

/-- Exact local residual of the finite joint trial wave. The three Taylor
remainders are the actual signed-collar operator's coefficient gaps. -/
theorem splitResidual_eq_dephased
    (hU : IsOpen U) (p : P) (ξ : P → X n)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ p i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,axis i))
    {K : Set (P × X n)} (hK : IsClosed K) (hKU : K ⊆ U)
    (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ q ∉ K, a q = 0)
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (M : ℕ)
    (A : RemainderMatrix n P) (τ : (P × X n) × ℝ → ℂ) (c : RemainderDrift n P)
    (RA : RemainderMatrix n P) (Rτ : (P × X n) × ℝ → ℂ) (Rc : RemainderDrift n P)
    {h : ℝ} (hh : h ≠ 0) {x : X n} (hx : x ∈ slice U p) (t : ℝ)
    (hSym : ∀ i j, A ((p,x),t) i j = A ((p,x),t) j i)
    (hA : A ((p,x),t) - (B.angularSlice p (fun i => ξ p i) hξ).matrixTaylor M x t =
      ((t : ℂ)^(M+1)) • RA ((p,x),t))
    (hτ : τ ((p,x),t) - (B.angularSlice p (fun i => ξ p i) hξ).normalTaylor M x t =
      (t : ℂ)^(M+1) * Rτ ((p,x),t))
    (hc : c ((p,x),t) - (B.angularSlice p (fun i => ξ p i) hξ).tangentTaylor M x t =
      ((t : ℂ)^(M+1)) • Rc ((p,x),t)) :
    (h : ℂ)^2 * complexSplitOperator (A ((p,x),t)) (τ ((p,x),t)) (c ((p,x),t))
      (fun q : X n × ℝ => B.finiteWave a η (planePhase ξ) M h ((p,q.1),q.2)) x t =
      Complex.exp (Complex.I * (planePhase ξ (p,x) / h : ℝ)) *
        B.dephasedResidual a η M RA Rτ τ Rc h ((p,x),t) := by
  rw [B.finiteWave_eq_slice hU hK hKU a ha ha0 η ξ p hξ hAxis M h]
  have hKU' : slice K p ⊆ slice U p := fun _ hx => hKU hx
  have ha' : ContDiffOn ℝ ∞ (fun y => a (p,y)) (slice U p) := contDiffOn_slice ha p
  have ha₀ : ∀ y ∉ slice K p, a (p,y) = 0 := fun y hy => ha0 (p,y) hy
  rw [(B.angularSlice p (fun i => ξ p i) hξ).finiteWave_residual_identity
    (isOpen_slice hU p) (isClosed_slice hK p) hKU' (fun y => a (p,y)) ha' ha₀ η hη M
    (A ((p,x),t)) hSym (τ ((p,x),t)) (c ((p,x),t)) hh hx t]
  dsimp only
  rw [tangentialWave,tangentialPhaseRead_eq_planePhase]
  unfold dephasedResidual
  dsimp only
  rw [hA,hτ,hc,B.finiteResidualProfile_slice hU p _ hξ hAxis hK ha ha0 M hx]
  simp only [B.taylorGapContribution_slice hU p _ hξ hAxis hK a ha ha0 RA Rτ Rc _ _
    hh hx t,
    B.cutoffContribution_slice hU p _ hξ hAxis hK a ha ha0 η τ _ h hx t]

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
