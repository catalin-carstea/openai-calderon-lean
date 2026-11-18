import Proof.OrthogonalAffineCoefficient
import Proof.AffineOperatorDerivativeBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL commonSupportMatrixFamily

lemma coefficientMatrixField_add_local (F G : SmoothCoefficientMatrix 2) (z : X) :
    coefficientMatrixField 2 (F+G) z = coefficientMatrixField 2 F z+coefficientMatrixField 2 G z := by
  ext i j
  rfl

/-- The actual geometric coefficient and its affine first correction admit
    genuine whole-angle native operator families with uniform first and
    quadratic Taylor derivative budgets. The same native coefficient witnesses
    serve the principal family and its Taylor residual. -/
theorem uniform_actual_rotated_operator_taylor_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ C ∧
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
          ell (OAI.AnisotropicCalderon.SmoothSphereRotation.coordinateRotation i j θ z) • (1:Mat)) ∧
        ContDiff ℝ ∞ (fun θ => strongDirichletOperator fixedSobolevCalculus 0 (F θ)) ∧
        ContDiff ℝ ∞ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (F θ)) ∧
        ContDiff ℝ ∞ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 θ)) ∧
        ‖fderiv ℝ (fun θ => strongDirichletOperator fixedSobolevCalculus 0 (F θ)) 0‖ ≤ C*r ∧
        ‖fderiv ℝ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 θ)) 0‖ ≤ C ∧
        ‖fderiv ℝ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (F θ)-
          fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)-
          r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 θ)) 0‖ ≤ C*r^2 := by
  have hRTheorem := uniform_actual_first_remainder_rotated_operator_C1 hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,CR,hηR,hCR,hRemainder⟩ := hRTheorem
  obtain ⟨F0,hF0⟩ := exists_flatCoefficientMatrix 2
  let PG := K^3*|M ⟨1,by omega⟩|
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let FB := fullC1OperatorBudget fixedSobolevCalculus
  have hPG : 0 ≤ PG := by dsimp [PG];positivity
  have hSB : 0 ≤ SB := strongC1OperatorBudget_nonneg _
  have hFB : 0 ≤ FB := fullC1OperatorBudget_nonneg _
  let C := 28*(SB+FB)*PG+CR+1
  have hC : 0 ≤ C := by dsimp [C];positivity
  refine ⟨min ηR 1,C,F0,lt_min hηR zero_lt_one,hC,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  dsimp only
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  have hCenter := hd.2.1.center_mem hy
  have hEll : ‖ell‖ ≤ PG := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
    have hEn := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
    have hD := (hd.1.firstMetricDensityFactor_jet_bounds hΩ
      (zero_lt_one.trans_le hK) (by omega) hCenter).1
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hD hEn (norm_nonneg _) (by positivity)).trans_eq (by dsimp [PG];ring))
  obtain ⟨aR,haR,SR,hSR,hzR,hRepR,hStrongR,hFullR⟩ :=
    hRemainder floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy i j
  obtain ⟨a1,ha1,S1,hS1,hz1,hRep1,hStrong1,hFull1⟩ := exists_rotated_linear_scalar_operator_family i j ell
  let FR := commonSupportMatrixFamily 2 aR haR SR hSR hzR
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let F : ℝ → SmoothCoefficientMatrix 2 := fun θ => c • F0+r • F1 θ+FR θ
  have hRStrongSmooth : ContDiff ℝ ∞ (fun θ => strongDirichletOperator fixedSobolevCalculus 0 (FR θ)) := contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 aR haR SR hSR hzR
  have h1StrongSmooth : ContDiff ℝ ∞ (fun θ => strongDirichletOperator fixedSobolevCalculus 0 (F1 θ)) := contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a1 ha1 S1 hS1 hz1
  have hRFullSmooth : ContDiff ℝ ∞ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (FR θ)) := contDiff_commonSupport_fullCoefficientOperator 0 aR haR SR hSR hzR
  have h1FullSmooth : ContDiff ℝ ∞ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 θ)) := contDiff_commonSupport_fullCoefficientOperator 0 a1 ha1 S1 hS1 hz1
  have hAS : (fun θ => strongDirichletOperator fixedSobolevCalculus 0 (F θ)) =
      fun θ => strongDirichletOperator fixedSobolevCalculus 0 (c • F0)+
        r • strongDirichletOperator fixedSobolevCalculus 0 (F1 θ)+strongDirichletOperator fixedSobolevCalculus 0 (FR θ) := by
    funext θ
    change (strongCoefficientOperatorL fixedSobolevCalculus 0) (c • F0+r • F1 θ+FR θ) =
      (strongCoefficientOperatorL fixedSobolevCalculus 0) (c • F0)+
        r • (strongCoefficientOperatorL fixedSobolevCalculus 0) (F1 θ)+
          (strongCoefficientOperatorL fixedSobolevCalculus 0) (FR θ)
    simp only [(strongCoefficientOperatorL fixedSobolevCalculus 0).map_add,
      (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul]
  have hAF : (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (F θ)) =
      fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)+
        r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 θ)+fullCoefficientOperatorL fixedSobolevCalculus 0 (FR θ) := by
    funext θ
    simp only [F,(fullCoefficientOperatorL fixedSobolevCalculus 0).map_add,
      (fullCoefficientOperatorL fixedSobolevCalculus 0).map_smul]
  have hFS : ContDiff ℝ ∞ (fun θ => strongDirichletOperator fixedSobolevCalculus 0 (F θ)) := by
    rw [hAS]
    have hScaled : ContDiff ℝ ∞ (fun θ : ℝ => r • strongDirichletOperator fixedSobolevCalculus 0 (F1 θ)) :=
      h1StrongSmooth.const_smul r
    have hConst : ContDiff ℝ ∞ (fun _ : ℝ => strongDirichletOperator fixedSobolevCalculus 0 (c • F0)) := contDiff_const
    exact (hConst.add hScaled).add hRStrongSmooth
  have hFF : ContDiff ℝ ∞ (fun θ => fullCoefficientOperatorL fixedSobolevCalculus 0 (F θ)) := by
    rw [hAF]
    have hScaled : ContDiff ℝ ∞ (fun θ : ℝ => r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 θ)) :=
      h1FullSmooth.const_smul r
    have hConst : ContDiff ℝ ∞ (fun _ : ℝ => fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)) := contDiff_const
    exact (hConst.add hScaled).add hRFullSmooth
  have hField (θ : ℝ) (z : X) (hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (FR θ) z =
      coefficientMatrixField 2 (F θ) z-coefficientMatrixField 2 (c • F0) z-r • coefficientMatrixField 2 (F1 θ) z := by
    simp only [F,coefficientMatrixField_add_local,coefficientMatrixField_smul]
    module
  obtain ⟨hDA,hDQ⟩ := coefficientOperators_affine_derivative_budget F F1 FR (c • F0)
    0 Set.univ isOpen_univ (mem_univ _) r (28*SB*‖ell‖) CR hr.le hr1
    (by positivity) hCR (fun θ _ => hField θ)
    (h1StrongSmooth.differentiable (by simp) 0) (hRStrongSmooth.differentiable (by simp) 0)
    hStrong1 hStrongR hFullR
  refine ⟨F,F1,?_,?_,hFS,hFF,h1FullSmooth,hDA.trans ?_,hFull1.trans ?_,hDQ.trans ?_⟩
  · intro θ z hz
    simp only [F,coefficientMatrixField_add_local,coefficientMatrixField_smul,hF0 z hz,
      F1,FR,coefficientMatrixField_commonSupportMatrixFamily,hRep1 θ z hz,hRepR θ z hz]
    exact (rotated_affineMatrixRemainder_identity i j
      (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r)) c r ell θ z).symm
  · intro θ z hz
    simpa only [F1,coefficientMatrixField_commonSupportMatrixFamily] using hRep1 θ z hz
  · have hCmp : 28*SB*‖ell‖+CR ≤ C := by
      have hN := mul_le_mul_of_nonneg_left hEll (by positivity : 0 ≤ 28*SB)
      dsimp only [C]
      nlinarith [mul_nonneg hFB hPG]
    exact mul_le_mul_of_nonneg_right hCmp hr.le
  · change 28*FB*‖ell‖ ≤ C
    have hN := mul_le_mul_of_nonneg_left hEll (by positivity : 0 ≤ 28*FB)
    dsimp only [C]
    nlinarith [mul_nonneg hSB hPG]
  · have hCmp : CR ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg (add_nonneg hSB hFB) hPG]
    exact mul_le_mul_of_nonneg_right hCmp (sq_nonneg r)

end ShrinkingSpheres
