import Proof.ActualRotatedOperatorTaylorData
import Proof.UniformStrongBulkTaylorData
import Proof.OperatorPoissonFamilyRegularity
import Proof.ActualRotatedDirichletInvertibility
import Proof.PoissonTaylorCutoffIndependence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local irreducible] strongCoefficientOperatorL fullCoefficientOperatorL

/-- The actual high radial quadratic Taylor remainder has a genuine smooth
    whole-angle family and a uniform radius-squared angle derivative bound.
    The inverse and bulk point bounds are transferred to exactly the same
    coefficient witnesses as the derivative bounds, using only unit-ball
    coefficient equality. Every admitted radius profile is covered. -/
theorem uniform_actual_high_radial_rotation_taylor {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CH : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ CH ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∃ F F1 : ℝ → SmoothCoefficientMatrix 2,
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → coefficientMatrixField 2 (F θ) z =
          coordinateRotationPrincipalFamily i j (fun v : ℝ × X =>
            principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) v.2) ((θ,0),z)) ∧
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → coefficientMatrixField 2 (F1 θ) z =
          ell (coordinateRotation i j θ z) • (1:Mat)) ∧
        (∀ θ,(strongDirichletOperator fixedSobolevCalculus 0 (F θ)).IsInvertible) ∧
        ContDiff ℝ ∞ (fun θ => actualHighRadialErrorL (F θ)-r • highFirstRadialVariationL F0 (F1 θ) c) ∧
        ‖fderiv ℝ (fun θ => actualHighRadialErrorL (F θ)-r • highFirstRadialVariationL F0 (F1 θ) c) 0‖ ≤ CH*r^2 := by
  have hTTheorem := uniform_actual_rotated_operator_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηT,CT,F0,hηT,hCT,hF0,hTData⟩ := hTTheorem
  have hBTheorem := uniform_actual_strong_bulk_taylor_data (Y:=Y) hΩ (by omega : 3 ≤ m) K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,CI,DB,V1,CS,G0,hηB,hCI,hDB,hV1,hCS,hG0,hBData⟩ := hBTheorem
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let CH := ‖fixedHalfOutwardTraceL‖*CI*
    ((CT+CT*CI*V1+DB*CI*CT)*‖fixedHarmonicLiftL‖+CT*CS)
  have hCH : 0 ≤ CH := by dsimp [CH];positivity
  refine ⟨min ηT (min ηB (min ηE 1)),CH,F0,
    lt_min hηT (lt_min hηB (lt_min hηE zero_lt_one)),hCH,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  dsimp only
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  have hST := hSmall.trans (min_le_left _ _)
  have hSB := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSE := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hS1 := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨F,F1,hRep,hRep1,hSmoothA,hSmoothT,hSmoothT1,hDA,hDT1,hDQ⟩ :=
    hTData floor hf ε hε hST d hd y hy i j
  obtain ⟨G,G1,hRepG,hRepG1,hInvG,hNIG,hInvG0,hNIG0,hNBG,hNVG1,hBulkG⟩ :=
    hBData floor hf ε hε hSB d hd y hy
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans hS1
  let H := framedNormalMetric d.g₁ d.frame d.expMap y r
  let KP := 4*K^2
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith [sq_nonneg (K-1)]
  have hEll : Elliptic (Metric.closedBall (0:X) 2) KP H :=
    hElliptic floor hf ε hε hSE d hd y hy d.g₁ (by simp)
  have hInv (θ : ℝ) : (strongDirichletOperator fixedSobolevCalculus 0 (F θ)).IsInvertible :=
    strongDirichletOperator_invertible_of_rotated_coefficient H KP hKP hEll i j θ (F θ)
      (fun z hz => hRep θ z (unitBall_subset_closedBall_two hz))
  have hFieldG : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (F 0) z = coefficientMatrixField 2 G z := by
    intro z hz
    rw [hRep 0 z (unitBall_subset_closedBall_two hz),coordinateRotationPrincipalFamily_zero_angle,
      hRepG z (unitBall_subset_closedBall_two hz)]
  have hFieldG1 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (F1 0) z = coefficientMatrixField 2 G1 z := by
    intro z hz
    rw [hRep1 0 z (unitBall_subset_closedBall_two hz),coordinateRotation_zero,
      hRepG1 z (unitBall_subset_closedBall_two hz)]
  have hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = coefficientMatrixField 2 G0 z := by
    intro z hz
    rw [hF0 z (unitBall_subset_closedBall_two hz),hG0 z (unitBall_subset_closedBall_two hz)]
  have hScalar : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (c • F0) z = coefficientMatrixField 2 (c • G0) z := by
    intro z hz
    rw [coefficientMatrixField_smul,coefficientMatrixField_smul,hFlat z hz]
  have hSG := (coefficientOperators_eq_of_unitBall fixedSobolevCalculus (F 0) G hFieldG).1
  have hSG0 := (coefficientOperators_eq_of_unitBall fixedSobolevCalculus (c • F0) (c • G0) hScalar).1
  have hTG1 := (coefficientOperators_eq_of_unitBall fixedSobolevCalculus (F1 0) G1 hFieldG1).2
  have hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible := by
    rw [hSG0]
    exact hInvG0
  have hNI : ‖(strongDirichletOperator fixedSobolevCalculus 0 (F 0)).inverse‖ ≤ CI := by
    rw [hSG]
    exact hNIG
  have hNI0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖ ≤ CI := by
    rw [hSG0]
    exact hNIG0
  have hNB : ‖strongDirichletOperator fixedSobolevCalculus 0 (F 0)-
      strongDirichletOperator fixedSobolevCalculus 0 (c • F0)‖ ≤ DB*r := by
    rw [hSG,hSG0]
    exact hNBG
  have hNV1 : ‖fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 0)‖ ≤ V1 := by
    rw [hTG1]
    exact hNVG1
  have hBulk : ‖strongPoissonL (F 0)-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 (F1 0) c‖ ≤ CS*r^2 := by
    rw [strongPoisson_first_remainder_eq_of_unitBall (F 0) G F0 G0 (F1 0) G1 c r hFieldG hFlat hFieldG1]
    exact hBulkG
  have hHigh : ContDiffOn ℝ ∞ (fun θ => actualHighRadialErrorL (F θ)) Set.univ :=
    contDiffOn_actualHighRadialErrorL_of_operators F Set.univ hSmoothA.contDiffOn hSmoothT.contDiffOn
      (fun θ _ => hInv θ)
  have hFirst := contDiffOn_highFirstRadialVariationL_of_operator F1 F0 c Set.univ hSmoothT1.contDiffOn
  have hSmooth : ContDiff ℝ ∞ (fun θ => actualHighRadialErrorL (F θ)-r • highFirstRadialVariationL F0 (F1 θ) c) :=
    contDiffOn_univ.mp (hHigh.sub (hFirst.const_smul r))
  have hBound := norm_actual_highRadial_first_remainder_derivative_le F F1 F0 c r
    0 Set.univ isOpen_univ (mem_univ _) (fun z hz => hF0 z (unitBall_subset_closedBall_two hz))
    (fun θ _ => hInv θ) hInv0
    (hSmoothA.differentiable (by simp) 0) (hSmoothT.differentiable (by simp) 0)
    (hSmoothT1.differentiable (by simp) 0)
    CI CI CT DB V1 CT CT CS hr.le hr1 hCI hCI hCT hDB hV1 hCT hCT hCS
    hNI hNI0 hDA hNB hNV1 hDT1 hDQ hBulk
  exact ⟨F,F1,hRep,hRep1,hInv,hSmooth,hBound⟩

end ShrinkingSpheres
