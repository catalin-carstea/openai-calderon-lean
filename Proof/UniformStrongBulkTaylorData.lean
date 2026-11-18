import Proof.StrongPoissonTaylorBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL

/-- Uniform point data for the true bulk Poisson Taylor remainder. The same
    actual coefficient witnesses carry inverse, affine and bulk remainder
    bounds; unit-ball congruence can transfer them to genuine angle families. -/
theorem uniform_actual_strong_bulk_taylor_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CI DB V1 CS : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ 0 ≤ CI ∧ 0 ≤ DB ∧ 0 ≤ V1 ∧ 0 ≤ CS ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∃ F F1 : SmoothCoefficientMatrix 2,
        (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F z =
          principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) z) ∧
        (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F1 z = ell z • (1:Mat)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ CI ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        ‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖ ≤ CI ∧
        ‖strongDirichletOperator fixedSobolevCalculus 0 F-
          strongDirichletOperator fixedSobolevCalculus 0 (c • F0)‖ ≤ DB*r ∧
        ‖fullCoefficientOperatorL fixedSobolevCalculus 0 F1‖ ≤ V1 ∧
        ‖strongPoissonL F-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 F1 c‖ ≤ CS*r^2 := by
  have hTheorem := uniform_first_strong_taylor_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηG,CI,P,Q,F0,hηG,hCI,hP,hQ,hF0,hData⟩ := hTheorem
  let B := fullC1OperatorBudget fixedSobolevCalculus
  let S := strongC1OperatorBudget fixedSobolevCalculus
  let DB := S*(Q+P)
  let V1 := B*P
  let CS := CI*(B*Q+CI*DB*V1)*‖fixedHarmonicLiftL‖
  have hB : 0 ≤ B := fullC1OperatorBudget_nonneg _
  have hS : 0 ≤ S := strongC1OperatorBudget_nonneg _
  have hDB : 0 ≤ DB := by dsimp [DB];positivity
  have hV1 : 0 ≤ V1 := by dsimp [V1];positivity
  have hCS : 0 ≤ CS := by dsimp [CS];positivity
  refine ⟨min ηG 1,CI,DB,V1,CS,F0,lt_min hηG zero_lt_one,hCI,hDB,hV1,hCS,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  obtain ⟨F,F1,hRep,hRep1,hInv,hNorm,hInv0,hNorm0,hVal1,hDeriv1,hValR,hDerivR⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let A := strongDirichletOperator fixedSobolevCalculus 0 F
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 (c • F0)
  let T := fullCoefficientOperatorL fixedSobolevCalculus 0 F
  let T0 := fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)
  let T1 := fullCoefficientOperatorL fixedSobolevCalculus 0 F1
  let R := F-c • F0-r • F1
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  have hq : 0 ≤ Q*r^2 := mul_nonneg hQ (sq_nonneg _)
  have hT1 : ‖T1‖ ≤ V1 := norm_fullCoefficientOperator_zero_le fixedSobolevCalculus F1 P hP hVal1 hDeriv1
  have hS1 : ‖strongDirichletOperator fixedSobolevCalculus 0 F1‖ ≤ S*P :=
    norm_strongDirichletOperator_zero_le fixedSobolevCalculus F1 P hP hVal1 hDeriv1
  have hTR : ‖T-T0-r • T1‖ ≤ (B*Q)*r^2 := by
    have hEq : T-T0-r • T1 = fullCoefficientOperatorL fixedSobolevCalculus 0 R := by
      dsimp only [R,T,T0,T1]
      simp only [(fullCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
        (fullCoefficientOperatorL fixedSobolevCalculus 0).map_smul]
    rw [hEq]
    exact (norm_fullCoefficientOperator_zero_le fixedSobolevCalculus R (Q*r^2) hq hValR hDerivR).trans_eq (by ring)
  have hAR : ‖strongDirichletOperator fixedSobolevCalculus 0 R‖ ≤ S*(Q*r^2) :=
    norm_strongDirichletOperator_zero_le fixedSobolevCalculus R (Q*r^2) hq hValR hDerivR
  have hADiff : ‖A-A0‖ ≤ DB*r := by
    have hEq : A-A0 = strongDirichletOperator fixedSobolevCalculus 0 R+
        r • strongDirichletOperator fixedSobolevCalculus 0 F1 := by
      have hMap : strongDirichletOperator fixedSobolevCalculus 0 R =
          A-A0-r • strongDirichletOperator fixedSobolevCalculus 0 F1 := by
        change (strongCoefficientOperatorL fixedSobolevCalculus 0) R =
          (strongCoefficientOperatorL fixedSobolevCalculus 0) F-
          (strongCoefficientOperatorL fixedSobolevCalculus 0) (c • F0)-
          r • (strongCoefficientOperatorL fixedSobolevCalculus 0) F1
        dsimp only [R]
        simp only [(strongCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
          (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul]
      rw [hMap]
      abel
    rw [hEq]
    calc
      _ ≤ ‖strongDirichletOperator fixedSobolevCalculus 0 R‖+
          ‖r • strongDirichletOperator fixedSobolevCalculus 0 F1‖ := norm_add_le _ _
      _ = ‖strongDirichletOperator fixedSobolevCalculus 0 R‖+
          r*‖strongDirichletOperator fixedSobolevCalculus 0 F1‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      _ ≤ S*(Q*r^2)+r*(S*P) := add_le_add hAR (mul_le_mul_of_nonneg_left hS1 hr.le)
      _ ≤ S*(Q*r)+r*(S*P) := by
        gcongr
        nlinarith only [mul_le_mul_of_nonneg_left hr1 hr.le]
      _ = _ := by dsimp [DB];ring
  have hPoisson := norm_strongPoisson_first_remainder_le F F0 F1 c r CI CI DB V1 (B*Q)
    hr.le hCI hCI hDB hV1 (by positivity)
    (fun z hz => hF0 z (unitBall_subset_closedBall_two hz)) hInv hInv0 hNorm hNorm0 hADiff hT1 hTR
  refine ⟨F,F1,?_,?_,hInv,hNorm,hInv0,hNorm0,hADiff,hT1,hPoisson⟩
  · intro z hz
    ext i j
    exact (hRep z hz i j).eq_of_nhds
  · intro z hz
    ext i j
    exact (hRep1 z hz i j).eq_of_nhds

end ShrinkingSpheres
