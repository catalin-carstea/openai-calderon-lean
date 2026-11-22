module

public import Proof.Manuscript.LowerGreen.BallCutoffChains
public import Proof.Manuscript.LowerGreen.NestedBallCutoffs

import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN CalderonN.BallDirichlet TauCeti
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

namespace SupportedBallFamily

variable (F : SupportedBallFamily P n) {p : P} (hp : p ∈ F.V)

@[expose] def cutoffData (χ u : SmoothData n) : SmoothData n := ⟨fun z => χ.1 z * u.1 z,χ.2.mul u.2⟩

include hp in
theorem forwardL_apply_localized
    (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (hSupp : tsupport χ.1 ⊆ ball (0 : X n) (1/2))
    (u v : SmoothData n)
    (hu : EqOn (negativeBallDivergence (fun z => F.a (p,z)) u.1) 0 (ball (0 : X n) 1))
    (hv : ∀ z ∈ tsupport χ.1, v.1 =ᶠ[𝓝 z] u.1) (s : ℕ) :
    F.forwardL s χ hχ p (smoothBallSobolev (s+1) v) =
      smoothBallSobolev (s+2) (cutoffData χ u) :=
  strongForwardCutoffL_apply_localized s F.a F.smooth F.K F.compact F.support χ hχ hSupp p
    (F.elliptic p hp) (fun z hz i j => (F.symmetry p hp z hz).apply j i) u v hu hv

theorem cutoffData_germ (χ u : SmoothData n) {x : X n} (h : χ.1 =ᶠ[𝓝 x] fun _ => 1) :
    (cutoffData χ u).1 =ᶠ[𝓝 x] u.1 := by
  filter_upwards [h] with z hz
  simp [cutoffData,hz]

include hp in
theorem forwardChainL_cutoff
    (χ : ℕ → SmoothData n) (hc : ∀ j, HasCompactSupport (χ j).1)
    (hSupp : ∀ j, tsupport (χ j).1 ⊆ ball (0 : X n) (1/2))
    (hNest : ∀ j, ∀ z ∈ tsupport (χ j).1, (χ (j+1)).1 =ᶠ[𝓝 z] fun _ => 1)
    (u : SmoothData n)
    (hu : EqOn (negativeBallDivergence (fun z => F.a (p,z)) u.1) 0 (ball (0 : X n) 1))
    (j m : ℕ) :
    F.forwardChainL χ hc p j m (smoothBallSobolev 1 (cutoffData (χ (j+m)) u)) =
      smoothBallSobolev (m+1) (cutoffData (χ j) u) := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih =>
    have hj : j + (m+1) = (j+1)+m := by omega
    rw [hj]
    change F.forwardL m (χ j) (hc j) p
      (F.forwardChainL χ hc p (j+1) m (smoothBallSobolev 1 (cutoffData (χ ((j+1)+m)) u))) = _
    rw [ih (j+1)]
    exact F.forwardL_apply_localized hp (χ j) (hc j) (hSupp j) u _ hu
      (fun z hz => cutoffData_germ _ _ (hNest j z hz)) m

end SupportedBallFamily

end CalderonPaper.LowerGreen

end
