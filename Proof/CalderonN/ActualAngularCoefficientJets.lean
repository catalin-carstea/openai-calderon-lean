module

public import Proof.CalderonN.BallRotationCoefficientBounds
public import Proof.CalderonN.ActualRadialWeightJets

import Mathlib.Tactic

/-! The angular generator of the normalized physical coefficient has
the scalar affine generator as its first term. The remainder is quadratic
in the radius in the local C1 norm. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 2350000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_angular_coefficient_jets (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η P Q : ℝ, 0 < η ∧ 0 ≤ P ∧ 0 ≤ Q ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let r := d.radius y
      let ell := firstDensityCenterLinear d y
      ‖ell‖ ≤ P ∧ ∀ A : X dim → Mat dim, ContDiff ℝ ∞ A →
        EqOn A (fun z => firstNormalVelocityCoefficient d y (r • frameVector d.frame y z))
          (ball (0 : X dim) (5/4)) →
        (∀ z ∈ closedBall (0 : X dim) 1, (A z).PosDef) ∧
        ∀ i j : Fin dim,
          let ellθ := ell.comp (ballRotationGeneratorL i j)
          let Rθ (z : X dim) := ballRotationCoefficient i j A z-r • (ellθ z • (1 : Mat dim))
          ‖ellθ‖ ≤ 2*P ∧ ∀ z ∈ closedBall (0 : X dim) 1,
            ‖Rθ z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ Rθ z‖ ≤ Q*r^2 := by
  obtain ⟨η,Q,hη,hQ,hQjet⟩ := uniform_normalized_coefficient_remainder_C2 (Y := Y)
    hn hΩ hm K ρ c₀ M Cj hK hρ 1 zero_le_one
  obtain ⟨ηP,P,hηP,hP,hPjet⟩ := uniform_actual_radial_weight_remainder (Y := Y)
    hn hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨min η ηP,P,(6+4*(dim : ℝ))*Q,lt_min hη hηP,hP,by positivity,?_⟩
  intro floor hf ε he hes d hd y hy
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  have hE : ‖ell‖ ≤ P :=
    (hPjet floor hf ε he (hes.trans (min_le_right _ _)) d hd y hy).1
  refine ⟨hE,?_⟩
  intro A hA hEq
  have hJ := hQjet floor hf ε he (hes.trans (min_le_left _ _)) d hd y hy
  have hInc : closedBall (0 : X dim) 1 ⊆ ball (0 : X dim) (5/4) :=
    closedBall_subset_ball (by norm_num)
  refine ⟨fun z hz => ?_,?_⟩
  · rw [hEq (hInc hz)]
    exact (hJ z hz).2.2.2.2
  intro i j
  let ellθ := ell.comp (ballRotationGeneratorL i j)
  let R (z : X dim) := A z-(1+r*ell z) • (1 : Mat dim)
  have hR : ContDiff ℝ ∞ R := hA.sub
    ((contDiff_const.add (contDiff_const.mul ell.contDiff)).smul contDiff_const)
  have hAg : A = fun z => (1+r*ell z) • (1 : Mat dim)+R z := by
    funext z
    dsimp only [R]
    abel
  have hRot : (fun z => ballRotationCoefficient i j A z-r • (ellθ z • (1 : Mat dim))) =
      ballRotationCoefficient i j R := by
    have hh := ballRotationCoefficient_affine i j ell r R hR
    rw [← hAg] at hh
    funext z
    rw [hh]
    change r • (ellθ z • (1 : Mat dim)) + ballRotationCoefficient i j R z -
      r • (ellθ z • (1 : Mat dim)) = _
    abel
  refine ⟨?_,?_⟩
  · exact ((ell.opNorm_comp_le _).trans (mul_le_mul hE
      (norm_ballRotationGeneratorL_le i j) (norm_nonneg _) hP)).trans_eq (mul_comm _ _)
  rw [show (fun z => ballRotationCoefficient i j A z -
      r • (ellθ z • (1 : Mat dim))) = ballRotationCoefficient i j R from hRot]
  intro z hz
  have hG : R =ᶠ[𝓝 z] normalizedFirstCoefficientRemainder d y := by
    filter_upwards [isOpen_ball.mem_nhds (hInc hz)] with w hw
    show A w-(1+r*ell w) • (1 : Mat dim) = _
    rw [hEq hw]
    rfl
  have hZ := hJ z hz
  have hzN : ‖z‖ ≤ 2 := (mem_closedBall_zero_iff.mp hz).trans (by norm_num)
  obtain ⟨hV,hD⟩ := norm_ballRotationCoefficient_jets_le i j hR z hzN
    (Q*r^2) (by positivity) (by rw [hG.eq_of_nhds]; exact hZ.2.1)
    (by rw [hG.fderiv_eq]; exact hZ.2.2.1)
    (by rw [(hG.fderiv).fderiv_eq]; exact hZ.2.2.2.1)
  rw [show ballRotationCoefficient i j A z-r • (ellθ z • (1 : Mat dim)) =
    ballRotationCoefficient i j R z from congrFun hRot z]
  change ‖ballRotationCoefficient i j R z‖ ≤ (6+4*(dim : ℝ))*Q*r^2 ∧
    ‖fderiv ℝ (ballRotationCoefficient i j R) z‖ ≤ (6+4*(dim : ℝ))*Q*r^2
  exact ⟨hV.trans_eq (by ring),hD.trans_eq (by ring)⟩

end CalderonN
