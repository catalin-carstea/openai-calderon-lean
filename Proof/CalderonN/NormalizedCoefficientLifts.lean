module

public import Proof.CalderonN.NormalizedCoefficientRemainderC2
public import Proof.CalderonN.CutoffCoefficientJets
public import Proof.CalderonN.BallRegularity.UniformStrongInverse

import Proof.CalderonN.FixedBallMetricEllipticity
import Proof.CalderonN.ThirdDerivativeProductBounds
import Proof.CalderonN.UniformFirstDensityTaylor
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim]

private theorem iteratedFDeriv_entry_le {f : X dim → Mat dim} {z : X dim}
    (hf : ContDiffAt ℝ ∞ f z) (k : ℕ) (i j : I dim) :
    ‖iteratedFDeriv ℝ k (fun w => f w i j) z‖ ≤ ‖iteratedFDeriv ℝ k f z‖ := by
  have hL : ‖matrixEntryL i j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro M
    exact (Matrix.norm_entry_le_entrywise_sup_norm M (i := i) (j := j)).trans_eq (one_mul _).symm
  have hh := (matrixEntryL i j).norm_iteratedFDeriv_comp_left hf (n := k) (by simp)
  have he : (matrixEntryL i j) ∘ f = fun w => f w i j :=
    funext fun w => matrixEntryL_apply i j (f w)
  rw [he] at hh
  exact hh.trans (mul_le_of_le_one_left (norm_nonneg _) hL)

/-- The compact extensions of the true coefficient and its affine model
agree on the unit ball. Their quadratic error is small in the same
coefficient norm used by the strong fixed-ball operator. -/
theorem uniform_normalized_coefficient_lifts (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η P Q : ℝ, 0 < η ∧ 0 ≤ P ∧ 0 ≤ Q ∧
      ∀ (F0 : SmoothCoefficientMatrix dim 2),
      (∀ x ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F0 x = 1) →
      ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F F1 : SmoothCoefficientMatrix dim 2,
        EqOn (coefficientMatrixField 2 F)
          (fun z => firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z))
          (ball (0 : X dim) (5/4)) ∧
        EqOn (coefficientMatrixField 2 F1) (fun z => firstDensityCenterLinear d y z • (1 : Mat dim))
          (ball (0 : X dim) (5/4)) ∧
        ‖F1‖ ≤ P ∧ ‖F-F0-(d.radius y) • F1‖ ≤ Q*(d.radius y)^2 ∧
        ∃ lo hi, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
          (coefficientMatrixField 2 F) lo hi := by
  obtain ⟨η,Q,hη,hQ,hTaylor⟩ := uniform_normalized_coefficient_remainder_C2 (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨θ,_,hθ,_,hDensity⟩ := uniform_first_density_taylor (Y := Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨C,hC,hLift⟩ := exists_uniform_cutoffCoefficientLifts dim
  let P := K^(dim-2)*(K^(dim-2)*((dim-2 : ℕ):ℝ)*K^2*|M ⟨1,by omega⟩|)
  have hK' : 0 < K := zero_lt_one.trans_le hK
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨min η θ,C*(2*P),C*Q,lt_min hη hθ,by positivity,by positivity,?_⟩
  intro F0 hF0 floor hf ε hε hεmin d hd y hy
  let r := d.radius y
  let R := normalizedFirstCoefficientRemainder d y
  let ell := firstDensityCenterLinear d y
  let A : X dim → Mat dim := fun z => ell z • 1
  let U := ball (0 : X dim) 2
  let V := ball (0 : X dim) (5/4)
  have hJ (z : X dim) (hz : z ∈ closedBall (0 : X dim) 2) :=
    hTaylor floor hf ε hε (hεmin.trans (min_le_left _ _)) d hd y hy z hz
  have hEll : ‖ell‖ ≤ P := by
    have hℓ : ell = (firstMetricDensityFactor d.γ d.g₁ y)⁻¹ • firstDensityCenterDerivative d y := rfl
    have hc : |(firstMetricDensityFactor d.γ d.g₁ y)⁻¹| ≤ K^(dim-2) := by
      rw [abs_of_pos (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))]
      exact hd.1.firstMetricDensityFactor_inverse_le hK' (hd.2.1.center_mem hy)
    have hb := (hDensity floor hf ε hε (hεmin.trans (min_le_right _ _)) d hd y hy).2.2.1
    rw [hℓ,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hc hb (norm_nonneg _) (by positivity)
  have hA (i j : I dim) : ContDiff ℝ ∞ (fun z => A z i j) := by
    change ContDiff ℝ ∞ (fun z => ell z * (1 : Mat dim) i j)
    exact ell.contDiff.mul contDiff_const
  have hAjet (i j : I dim) (z : X dim) (hz : z ∈ U) (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (fun w => A w i j) z‖ ≤ 2*P := by
    let T : X dim →L[ℝ] ℝ := ((1 : Mat dim) i j) • ell
    have hTn : ‖T‖ ≤ P := by
      have hIJ : |(1 : Mat dim) i j| ≤ 1 := by
        simp only [Matrix.one_apply]
        split_ifs <;> norm_num
      rw [show T = ((1 : Mat dim) i j) • ell from rfl,norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul hIJ hEll (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have he : (fun z => A z i j) = T := by
      funext z
      change ell z * (1 : Mat dim) i j = (1 : Mat dim) i j * ell z
      ring
    rw [he]
    have hzN : ‖z‖ ≤ 2 := by simpa only [U,mem_ball,dist_zero_right] using le_of_lt (show dist z 0 < 2 from hz)
    rcases k with _ | _ | _ | k
    · rw [norm_iteratedFDeriv_zero]
      exact (T.le_opNorm z).trans ((mul_le_mul hTn hzN (norm_nonneg _) hP).trans_eq (mul_comm _ _))
    · rw [norm_iteratedFDeriv_one,ContinuousLinearMap.fderiv]
      linarith
    · rw [norm_iteratedFDeriv_two_eq_nested,show fderiv ℝ (⇑T) = fun _ => T from funext fun _ => T.fderiv]
      simp only [fderiv_fun_const,Pi.zero_apply,norm_zero]
      positivity
    · omega
  have hR (i j : I dim) : ContDiffOn ℝ ∞ (fun z => R z i j) U := by
    intro z hz
    exact ((matrixEntryL i j).contDiff.contDiffAt.comp z (hJ z (ball_subset_closedBall hz)).1).contDiffWithinAt
  have hRjet (i j : I dim) (z : X dim) (hz : z ∈ U) (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (fun w => R w i j) z‖ ≤ Q*r^2 := by
    have hh := hJ z (ball_subset_closedBall hz)
    refine (iteratedFDeriv_entry_le hh.1 k i j).trans ?_
    rcases k with _ | _ | _ | k
    · rw [norm_iteratedFDeriv_zero]
      exact hh.2.1
    · rw [norm_iteratedFDeriv_one]
      exact hh.2.2.1
    · rw [norm_iteratedFDeriv_two_eq_nested]
      exact hh.2.2.2.1
    · omega
  obtain ⟨F1,hF1,hF1val⟩ := hLift A (2*P) (by positivity) (fun i j => (hA i j).contDiffOn) hAjet
  obtain ⟨FR,hFR,hFRval⟩ := hLift R (Q*r^2) (by positivity) hR hRjet
  let F := F0+r • F1+FR
  have hF : EqOn (coefficientMatrixField 2 F)
      (fun z => firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)) V := by
    intro z hz
    have hz2 : z ∈ closedBall (0 : X dim) 2 :=
      ball_subset_closedBall (ball_subset_ball (by norm_num : (5/4 : ℝ) ≤ 2) hz)
    have h₀ := hF0 z hz2
    have h₁ := hF1val hz
    have h₂ := hFRval hz
    ext i j
    change coefficientValue 2 ((F0 i j+r • F1 i j)+FR i j) z = _
    rw [coefficientValue_add,coefficientValue_add,coefficientValue_smul]
    change coefficientMatrixField 2 F0 z i j+r*coefficientMatrixField 2 F1 z i j+
      coefficientMatrixField 2 FR z i j = _
    rw [h₀,h₁,h₂]
    simp only [A,R,normalizedFirstCoefficientRemainder,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]
    ring
  have hErr : F-F0-r • F1 = FR := by
    dsimp only [F]
    abel
  refine ⟨F,F1,hF,hF1val,hF1,?_,?_⟩
  · rw [hErr]
    exact hFR.trans_eq (by ring)
  · apply exists_uniformEllipticOn_fixedBall (coefficientMatrixField 2 F)
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (contDiff_coefficientValue 2 (F i j)).continuous
    · intro z hz
      have hzV : z ∈ V := closedBall_subset_ball (by norm_num : (1 : ℝ) < 5/4) hz
      rw [hF hzV]
      exact (hJ z (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)).2.2.2.2

end CalderonN
