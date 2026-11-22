module

public import Proof.CalderonN.NativeCoefficientSmoothBounds
public import Proof.CalderonN.NormalizedCoefficientLifts

import Proof.CalderonN.BallRegularity.UniformStrongInverse
import Mathlib.Tactic

/-! Uniform weak coercivity and strong inverses for the same
normalized compact coefficient Taylor family. -/

public section

noncomputable section
open Set Metric
open scoped ENNReal ContDiff Matrix.Norms.Elementwise InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_normalized_ballTaylor_budgets (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ (F₀ : SmoothCoefficientMatrix dim 2) (η P Q Inv : ℝ),
      (∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F₀ z = 1) ∧
      0 < η ∧ 0 ≤ P ∧ 0 ≤ Q ∧ 0 ≤ Inv ∧
      ‖(strongDirichletOperator fixedSobolevCalculus 0 F₀).inverse‖ ≤ Inv ∧
      (∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
        Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
        let r := d.radius y
        let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
        let ell := firstDensityCenterLinear d y
        ∃ (F F₁ : SmoothCoefficientMatrix dim 2) (lo hi : ℝ),
          EqOn (coefficientMatrixField 2 F) a (ball (0 : X dim) (5/4)) ∧
          EqOn (coefficientMatrixField 2 F₁) (fun z => ell z • (1 : Mat dim)) (ball (0 : X dim) (5/4)) ∧
          UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi ∧
          ‖F₁‖ ≤ P ∧ ‖F-F₀‖ ≤ (P+Q)*r ∧ ‖F-F₀-r • F₁‖ ≤ Q*r^2 ∧
          ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ Inv ∧
          let E := fixedBallSmoothEnergyL (contDiff_coefficientMatrixField 2 F).continuous
          let E₁ := fixedBallSmoothEnergyL (ell.continuous.smul
            (show Continuous (fun _ : X dim => (1 : Mat dim)) from continuous_const))
          ‖E₁‖ ≤ (dim:ℝ)^2*P ∧
          ‖E-fixedBallFlatEnergyL dim‖ ≤ (dim:ℝ)^2*(P+Q)*r ∧
          ‖E-fixedBallFlatEnergyL dim-r • E₁‖ ≤ (dim:ℝ)^2*Q*r^2 ∧
          ∀ v : FixedBallH1Zero dim,
            (1/10:ℝ)*‖v‖^2 ≤ E (v : FixedBallH1 dim) (v : FixedBallH1 dim)) := by
  obtain ⟨η,P,Q,hη,hP,hQ,hLift⟩ := uniform_normalized_coefficient_lifts (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨F₀,hF₀,δ,Inv,hδ,hInv,hInverse⟩ := exists_uniform_strongDirichlet_neighborhood dim 0
  let G := (dim:ℝ)^2*(P+Q)
  let θ := δ/(P+Q+1)
  let κ := (1/10:ℝ)/(G+1)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hEll₀ : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F₀) 1 1 := by
    have h := uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))
    refine ⟨h.1,h.2.1,fun z hz => ?_⟩
    rw [hF₀ z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (ball_subset_closedBall hz))]
    exact h.2.2 hz
  refine ⟨F₀,min η (min 1 (min θ κ)),P,Q,Inv,hF₀,
    lt_min hη (lt_min zero_lt_one (lt_min (by dsimp [θ]; positivity) (by dsimp [κ]; positivity))),
    hP,hQ,hInv,hInverse F₀ 1 1 (by rw [sub_self,norm_zero]; exact hδ.le) hEll₀,?_⟩
  intro floor hf ε he hs d hd y hy
  dsimp only
  let r := d.radius y
  let ell := firstDensityCenterLinear d y
  obtain ⟨F,F₁,hF,hF₁,hF₁N,hFRN,lo,hi,hEll⟩ :=
    hLift F₀ hF₀ floor hf ε he (hs.trans (min_le_left _ _)) d hd y hy
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε :=
    (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have htail := hs.trans (min_le_right _ _)
  have hr₁ : r ≤ 1 := hrε.trans (htail.trans (min_le_left _ _))
  have hsmall := htail.trans (min_le_right _ _)
  have hrδ := (le_div_iff₀ (show 0 < P+Q+1 by positivity)).mp
    (hrε.trans (hsmall.trans (min_le_left _ _)))
  have hrκ := (le_div_iff₀ (show 0 < G+1 by positivity)).mp
    (hrε.trans (hsmall.trans (min_le_right _ _)))
  have hNear : ‖F-F₀‖ ≤ (P+Q)*r := by
    rw [show F-F₀ = (F-F₀-r • F₁)+r • F₁ by abel]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hN := add_le_add hFRN (mul_le_mul_of_nonneg_left hF₁N hr.le)
    exact hN.trans (by nlinarith [mul_nonneg (mul_nonneg hQ hr.le) (sub_nonneg.mpr hr₁)])
  have hInvF : ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ Inv :=
    hInverse F lo hi (hNear.trans (by nlinarith)) hEll
  refine ⟨F,F₁,lo,hi,hF,hF₁,hEll,hF₁N,hNear,hFRN,hInvF,?_⟩
  let A := coefficientMatrixField 2 F
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ : X dim → Mat dim := fun z => ell z • 1
  have hA : ContDiff ℝ ∞ A := contDiff_coefficientMatrixField 2 F
  have hA₀ : Continuous A₀ := continuous_const
  have hA₁ : ContDiff ℝ ∞ A₁ := ell.contDiff.smul contDiff_const
  let E := fixedBallSmoothEnergyL hA.continuous
  let E₀ := fixedBallFlatEnergyL dim
  let E₁ := fixedBallSmoothEnergyL hA₁.continuous
  have hBall : ball (0 : X dim) 1 ⊆ ball (0 : X dim) (5/4) := ball_subset_ball (by norm_num)
  have hF₀eq (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : coefficientMatrixField 2 F₀ z = A₀ z :=
    hF₀ z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2) (ball_subset_closedBall hz))
  have hFeq (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      coefficientMatrixField 2 (F-F₀) z = (A-A₀) z := by
    rw [coefficientMatrixField_two_sub]
    change A z-coefficientMatrixField 2 F₀ z = A z-A₀ z
    rw [hF₀eq z hz]
  have hReq (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      coefficientMatrixField 2 (F-F₀-r • F₁) z = (A-A₀-r • A₁) z := by
    rw [coefficientMatrixField_two_sub,coefficientMatrixField_two_smul]
    change coefficientMatrixField 2 (F-F₀) z-r • coefficientMatrixField 2 F₁ z =
      (A-A₀) z-r • A₁ z
    rw [hFeq z hz,hF₁ (hBall hz)]
  have hN₁ : ‖E₁‖ ≤ (dim:ℝ)^2*P :=
    norm_fixedBallSmoothEnergy_of_native_bound F₁ hA₁.continuous P hF₁N (hF₁.mono hBall)
  have hNE : ‖E-E₀‖ ≤ G*r := by
    have h := norm_fixedBallSmoothEnergy_of_native_bound (F-F₀)
      (hA.continuous.sub (continuous_const (y:=(1:Mat dim)))) _ hNear hFeq
    rw [fixedBallSmoothEnergyL_sub hA.continuous hA₀,← fixedBallFlatEnergyL] at h
    exact h.trans_eq (by dsimp [G]; ring)
  have hNR : ‖E-E₀-r • E₁‖ ≤ (dim:ℝ)^2*Q*r^2 := by
    have h := norm_fixedBallSmoothEnergy_of_native_bound (F-F₀-r • F₁)
      ((hA.continuous.sub (continuous_const (y:=(1:Mat dim)))).sub (hA₁.continuous.const_smul r))
      _ hFRN hReq
    rw [fixedBallSmoothEnergyL_sub (hA.continuous.sub hA₀) (hA₁.continuous.const_smul r),
      fixedBallSmoothEnergyL_sub hA.continuous hA₀,← fixedBallFlatEnergyL,fixedBallSmoothEnergyL_smul hA₁.continuous r] at h
    exact h.trans_eq (by ring)
  refine ⟨hN₁,hNE,hNR,fun v => ?_⟩
  let j := fixedBallZeroInclusionL dim
  have hFlat : (1/5:ℝ)*‖v‖*‖v‖ ≤ E₀ (j v) (j v) :=
    fixedBallSmoothEnergy_zero_coercive continuous_const
      (uniformlyEllipticOn_const_one_one (n:=Fin dim) (fixedBallOpens dim : Set (X dim))) v
  have hJ : ‖j v‖ = ‖v‖ := rfl
  have hDiff : ‖(E-E₀) (j v) (j v)‖ ≤ (1/10:ℝ)*‖v‖*‖v‖ := by
    rw [← hJ]
    exact ((E-E₀).le_opNorm₂ _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hNE.trans (by nlinarith)) (norm_nonneg _))
        (norm_nonneg _))
  simp only [sub_apply,Real.norm_eq_abs] at hDiff
  change (1/10:ℝ)*‖v‖^2 ≤ E (j v) (j v)
  nlinarith only [hFlat,(abs_le.mp hDiff).1]

end CalderonN
