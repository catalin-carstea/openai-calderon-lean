module

public import Proof.CalderonN.MultiplierForcingEstimate

import Mathlib.Tactic

/-! Smooth representatives of the source terms used with the native
strong inverse. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothMultiplierForcing {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (m u : SmoothData dim) : SmoothData dim := by
  let S := fun z : X dim => ∑ i, ∑ j, A z i j*coordDeriv i m.1 z*coordDeriv j u.1 z
  have hS : ContDiff ℝ ∞ S := by
    dsimp only [S]
    apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    have ha : ContDiff ℝ ∞ (fun z => A z i j) := contDiff_pi.mp (contDiff_pi.mp hA i) j
    exact (ha.mul (smoothDataCoordDeriv i m).2).mul (smoothDataCoordDeriv j u).2
  exact ⟨greenSourceCutoffError A m.1 u.1,
    (u.2.mul (contDiff_negativeBallDivergence hA m.2)).sub (contDiff_const.mul hS)⟩

@[expose] def smoothDivergenceForcing {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (u : SmoothData dim) : SmoothData dim :=
  ⟨negativeBallDivergence A u.1,contDiff_negativeBallDivergence hA u.2⟩

theorem norm_smoothMultiplierForcing_le {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (m u : SmoothData dim) (C J : ℝ) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (hEntry : ∀ z ∈ ball (0 : X dim) 1, ∀ i j,
      |A z i j| ≤ C ∧ ‖fderiv ℝ (fun x => A x i j) z‖ ≤ C)
    (hM : ∀ z ∈ ball (0 : X dim) 1, ‖fderiv ℝ m.1 z‖ ≤ J ∧
      ∀ i, ‖fderiv ℝ (coordDeriv i m.1) z‖ ≤ J) :
    ‖smoothBallSobolev 0 (smoothMultiplierForcing hA m u)‖ ≤ (4*(dim:ℝ)^2*C*J)*‖smoothSobolev u‖ := by
  obtain ⟨F,hF,hBound⟩ := norm_multiplier_forcing_le hA m u C J hC hJ hEntry hM
  rw [smoothBallSobolev_eq_of_eqOn_ball 0 (smoothMultiplierForcing hA m u) F
    (fun z _ => by
      change greenSourceCutoffError A m.1 u.1 z = F.1 z
      exact (congrFun hF z).symm)]
  exact hBound

end CalderonN
