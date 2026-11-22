module

public import Proof.CalderonN.SmoothMultiplierForcing
public import Proof.CalderonN.NativeWeakHarmonicResponse
public import Proof.CalderonN.NormalizedStrongPoissonTaylor

import Mathlib.Tactic

/-! Restriction of the native coefficient jets gives the pointwise
bounds and the strong and weak graph bounds on the same unit ball. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem native_coefficientMatrix_entry_bound (F : SmoothCoefficientMatrix dim 2)
    (z : X dim) (i j : Fin dim) :
    |coefficientMatrixField 2 F z i j| ≤ ‖F‖ ∧
      ‖fderiv ℝ (fun x => coefficientMatrixField 2 F x i j) z‖ ≤ ‖F‖ := by
  have hF := (norm_le_pi_norm (F i) j).trans (norm_le_pi_norm F i)
  have h₀ := (norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 0 (by omega) z).trans hF
  have h₁ := (norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 1 (by omega) z).trans hF
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h₀
  rw [norm_iteratedFDeriv_one] at h₁
  exact ⟨h₀,h₁⟩

theorem coefficientMatrixField_two_sub (F G : SmoothCoefficientMatrix dim 2) :
    coefficientMatrixField 2 (F-G) = coefficientMatrixField 2 F-coefficientMatrixField 2 G := by
  funext z
  ext i j
  unfold coefficientMatrixField coefficientValue
  rfl

theorem coefficientMatrixField_two_smul (r : ℝ) (F : SmoothCoefficientMatrix dim 2) :
    coefficientMatrixField 2 (r • F) = r • coefficientMatrixField 2 F := by
  funext z
  ext i j
  unfold coefficientMatrixField coefficientValue
  rfl

theorem coefficientEntry_bounds_of_eqOn_native
    (F : SmoothCoefficientMatrix dim 2) {A : X dim → Mat dim} (C : ℝ) (hC : ‖F‖ ≤ C)
    (hEq : EqOn (coefficientMatrixField 2 F) A (ball (0 : X dim) 1)) :
    ∀ z ∈ ball (0 : X dim) 1, ∀ i j,
      |A z i j| ≤ C ∧ ‖fderiv ℝ (fun x => A x i j) z‖ ≤ C := by
  intro z hz i j
  have hG : (fun x => coefficientMatrixField 2 F x i j) =ᶠ[𝓝 z] fun x => A x i j := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx
    rw [hEq hx]
  have h := native_coefficientMatrix_entry_bound F z i j
  rw [hG.eq_of_nhds,hG.fderiv_eq] at h
  exact ⟨h.1.trans hC,h.2.trans hC⟩

theorem norm_smoothDivergenceForcing_le_of_native_bound
    (F : SmoothCoefficientMatrix dim 2) {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (C : ℝ) (hC : ‖F‖ ≤ C) (hEq : EqOn (coefficientMatrixField 2 F) A (ball (0 : X dim) 1))
    (u : SmoothData dim) :
    ‖smoothBallSobolev 0 (smoothDivergenceForcing hA u)‖ ≤
      (‖fullBallCoefficientOperatorL dim 0‖*C)*‖smoothBallSobolev 2 u‖ := by
  obtain ⟨hFs,hNative⟩ := fullBallDivergence_native_smooth 0 F u
  let v : SmoothData dim := ⟨negativeBallDivergence (coefficientMatrixField 2 F) u.1,hFs⟩
  have hV : EqOn (smoothDivergenceForcing hA u).1 v.1 (ball (0 : X dim) 1) := by
    intro z hz
    have hG : coefficientMatrixField 2 F =ᶠ[𝓝 z] A := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hEq hw
    exact (negativeBallDivergence_congr_germ hG (EventuallyEq.rfl (f:=u.1))).symm
  rw [smoothBallSobolev_eq_of_eqOn_ball 0 _ _ hV,show smoothBallSobolev 0 v =
    fullBallDivergenceL 0 F (smoothBallSobolev 2 u) from hNative.symm,← fullBallCoefficientOperatorL_apply]
  exact ((fullBallCoefficientOperatorL dim 0 F).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (((fullBallCoefficientOperatorL dim 0).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hC (norm_nonneg _))) (norm_nonneg _))

theorem norm_fixedBallSmoothEnergy_of_native_bound
    (F : SmoothCoefficientMatrix dim 2) {A : X dim → Mat dim} (hA : Continuous A)
    (C : ℝ) (hC : ‖F‖ ≤ C) (hEq : EqOn (coefficientMatrixField 2 F) A (ball (0 : X dim) 1)) :
    ‖fixedBallSmoothEnergyL hA‖ ≤ (dim:ℝ)^2*C := by
  apply norm_fixedBallSmoothEnergyL_le hA C ((norm_nonneg _).trans hC)
  exact fun z hz i j => (coefficientEntry_bounds_of_eqOn_native F C hC hEq z hz i j).1

end CalderonN
