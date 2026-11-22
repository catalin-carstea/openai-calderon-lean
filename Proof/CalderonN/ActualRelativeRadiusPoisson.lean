module

public import Proof.CalderonN.RelativeRadiusStrongPoisson

import Proof.CalderonN.FixedBallMetricEllipticity
import Mathlib.Tactic

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The actual relative-radius derivative of the normalized fixed-ball
Poisson remainder satisfies a uniform quadratic bound. -/
theorem uniform_relativeRadius_poisson_first_variation (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ F0 : SmoothCoefficientMatrix dim 2,
      (∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F0 z = 1) ∧
      ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F1 : SmoothCoefficientMatrix dim 2,
        EqOn (coefficientMatrixField 2 F1)
          (fun z => firstDensityCenterLinear d y z • (1 : Mat dim))
          (ball (0 : X dim) (5/4)) ∧
        ∃ a : ℝ × X dim → Mat dim, ∃ ha : ContDiff ℝ ∞ a,
        ∃ J : Set (X dim), ∃ hJ : IsCompact J, ∃ hS : ∀ t z, z ∉ J → a (t,z) = 0,
          (∀ t ∈ ball (0 : ℝ) (1/16), ∀ z ∈ ball (0 : X dim) (9/8),
            a (t,z) = relativeRadiusCoefficient d y t z) ∧
          ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
            (P0 : H →L[ℝ] BallSobolev dim 2),
            (fullBallDivergenceL 0 F0).comp P0 = 0 →
            let F := commonSupportMatrixFamily 2 a ha J hJ hS
            let j := (strongDirichletSubmodule dim 0).toSubmodule.subtypeL
            let I₀ := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
            let P1 := -(j.comp (I₀.comp ((fullBallDivergenceL 0 F1).comp P0)))
            ‖fderiv ℝ (fun t => (ballPoissonOperatorL 0 (F t)).comp P0-P0-
            ((1+t)*d.radius y) • P1) 0‖ ≤ B * ‖P0‖ * (d.radius y)^2 := by
  obtain ⟨η,P,Q,hη,hP,hQ,hLift⟩ := uniform_normalized_coefficient_lifts (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨F0,hF0,δ,C,hδ,hC,hInv⟩ := exists_uniform_strongDirichlet_neighborhood dim 0
  obtain ⟨ηR,B₁,B₂,hηR,hB₁,hB₂,hRel⟩ :=
    uniform_relativeRadius_strong_coefficient (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  let τ := min ηR (min η (min 1 (δ/(P+Q+1))))
  let S := strongCoefficientOperatorL (dim := dim) fixedSobolevCalculus 0
  let T := fullBallCoefficientOperatorL dim 0
  let D := ‖S‖*(P+Q)
  let L := ‖T‖*P
  let R := ‖T‖*Q
  let V := ‖S‖*P
  let B := C*(B₂+(B₁+V)*C*L+D*C*L+(B₁+V)*C*(R+C*D*L))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hτ : 0 < τ := lt_min hηR (lt_min hη (lt_min zero_lt_one (div_pos hδ (by positivity))))
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
  have hUE0 : TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (coefficientMatrixField 2 F0) 1 1 := by
    have h := TauCeti.PDE.uniformlyEllipticOn_const_one_one (n := Fin dim) (fixedBallOpens dim : Set (X dim))
    refine ⟨h.1,h.2.1,?_⟩
    intro z hz
    rw [hF0 z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (ball_subset_closedBall hz))]
    exact h.2.2 hz
  have hA0 : A0.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 F0 hUE0
  have hAI₀ : ‖A0.inverse‖ ≤ C :=
    hInv F0 1 1 (by rw [sub_self,norm_zero]; exact hδ.le) hUE0
  refine ⟨F0,hF0,τ,B,hτ,hB,?_⟩
  intro floor hf ε hε hετ d hd y hy
  have hεR : ε ≤ ηR := hετ.trans (min_le_left _ _)
  have hετ' : ε ≤ min η (min 1 (δ/(P+Q+1))) := hετ.trans (min_le_right _ _)
  obtain ⟨F,F1,hF,hF1,hF1n,hErr,lo,hi,hUE⟩ :=
    hLift F0 hF0 floor hf ε hε (hετ'.trans (min_le_left _ _)) d hd y hy
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans
    (hd.2.2.2.2.2 y hy).2
  have hr1 : r ≤ 1 := hrε.trans (hετ'.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hNear : ‖F-F0‖ ≤ (P+Q)*r := by
    have he : F-F0 = (F-F0-r • F1)+r • F1 := by abel
    rw [he]
    have hScale : ‖r • F1‖ ≤ r*P := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hF1n hr.le
    calc
      _ ≤ ‖F-F0-r • F1‖+‖r • F1‖ := norm_add_le _ _
      _ ≤ Q*r^2+r*P := add_le_add hErr hScale
      _ ≤ (P+Q)*r := by
        have hh := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ Q*r by positivity)
        nlinarith only [hh]
  have hrδ : r ≤ δ/(P+Q+1) := hrε.trans (hετ'.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ' : ‖F-F0‖ ≤ δ := by
    have h := (le_div_iff₀ (by positivity : 0 < P+Q+1)).mp hrδ
    exact hNear.trans (by linarith)
  let A := strongDirichletOperator fixedSobolevCalculus 0 F
  have hA : A.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity 0 F hUE
  have hAI : ‖A.inverse‖ ≤ C := hInv F lo hi hδ' hUE
  have hAD : ‖A-A0‖ ≤ D*r := by
    have he : A-A0 = S (F-F0) := (map_sub S F F0).symm
    rw [he]
    exact (S.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hNear (norm_nonneg _)).trans_eq (by dsimp [D];ring))
  have hTL : ‖T F1‖ ≤ L := (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hF1n (norm_nonneg _))
  have hTR : ‖T F-T F0-r • T F1‖ ≤ R*r^2 := by
    rw [← map_smul T,← map_sub T,← map_sub T]
    exact (T.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hErr (norm_nonneg _)).trans_eq (by dsimp [R];ring))
  obtain ⟨a,ha,J,hJ,hS,hAt,hReal,hBAS,hBAT⟩ :=
    hRel floor hf ε hε hεR d hd y hy F F1 hF hF1
  have hStrong₁ : ‖S F1‖ ≤ V :=
    (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left hF1n (norm_nonneg _))
  refine ⟨F1,hF1,a,ha,J,hJ,hS,hReal,?_⟩
  intro H _ _ P0 hFlat
  have hPoint : let F := commonSupportMatrixFamily 2 a ha J hJ hS 0
      let A := strongDirichletOperator fixedSobolevCalculus 0 F
      let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
      A.IsInvertible ∧ ‖A.inverse‖ ≤ C ∧ ‖A-A0‖ ≤ D*r ∧
      ‖fullBallDivergenceL 0 F-fullBallDivergenceL 0 F0-r • fullBallDivergenceL 0 F1‖ ≤ R*r^2 := by
    dsimp only
    rw [hAt]
    exact ⟨hA,hAI,hAD,hTR⟩
  exact norm_relativeRadius_poisson_taylor_derivative_le a ha J hJ hS F0 F1 P0 hFlat
    r C D L R B₁ B₂ V hr.le hr1 hC hD hL hR hB₁ hB₂ hV hA0 hAI₀ hTL hStrong₁ hPoint ⟨hBAS,hBAT⟩

end CalderonN
