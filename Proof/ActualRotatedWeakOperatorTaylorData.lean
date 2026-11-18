import Proof.UniformRotatedWeakEnergy
import Proof.FirstScalarWeakEnergyFamily
import Proof.AffineCommonSupportMatrixFamily
import Proof.AffineWeakEnergyFamilyIdentity
import Proof.AffineFamilyDerivativeBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

/-- Genuine whole-angle actual coefficient witnesses carry uniform principal,
    first-model and quadratic residual native weak operator derivative bounds.
    Every admitted radius and arbitrary smooth orthonormal frame is covered. -/
theorem uniform_actual_rotated_weak_operator_taylor_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
        ∃ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      ∃ a1 : ℝ × X → Mat,∃ ha1 : ContDiff ℝ ∞ a1,∃ S1 : Set X,∃ hS1 : IsCompact S1,
        ∃ hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0,
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
          (fun v : ℝ × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) v.2) ((θ,0),z)) ∧
        (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a1 (θ,z) = ell (coordinateRotation i j θ z) • (1:Mat)) ∧
        ‖fderiv ℝ (commonSupportZeroWeakEnergy a ha) 0‖ ≤ C*r ∧
        ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ C*r ∧
        ‖fderiv ℝ (commonSupportWeakEnergy a1 ha1) 0‖ ≤ C ∧
        ‖fderiv ℝ (fun θ => commonSupportWeakEnergy a ha θ-
          nativeCoefficientWeakEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)-
          r • commonSupportWeakEnergy a1 ha1 θ) 0‖ ≤ C*r^2 ∧
        ‖fderiv ℝ (fun θ => commonSupportFullWeakEnergy a ha θ-
          TauCeti.PDE.energyFormH1L (flatCoefficientBound c)-
          r • commonSupportFullWeakEnergy a1 ha1 θ) 0‖ ≤ C*r^2 := by
  have hRTheorem := uniform_actual_rotated_remainder_weakEnergy_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,CR,hηR,hCR,hRData⟩ := hRTheorem
  let PG := K^3*|M ⟨1,by omega⟩|
  let CF := 14*weakFullDerivativeBudget*PG
  let C := CF+CR+1
  have hPG : 0 ≤ PG := by dsimp [PG];positivity
  have hCF : 0 ≤ CF := by dsimp [CF];exact mul_nonneg (mul_nonneg (by norm_num) weakFullDerivativeBudget_nonneg) hPG
  have hC : 0 ≤ C := by dsimp [C];positivity
  refine ⟨min ηR 1,C,lt_min hηR zero_lt_one,hC,?_⟩
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
  have hRemPoint := hRData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy i j
  obtain ⟨aR,haR,SR,hSR,hzR,hRepR,hRFull,hRWeak,hRZero⟩ := hRemPoint
  have hFirstTheorem := exists_rotated_linear_scalar_weakEnergy_family i j ell
  obtain ⟨a1,ha1,S1,hS1,hz1,hRep1,h1Full,h1Weak,h1Zero⟩ := hFirstTheorem
  have hFirstBound : 14*weakFullDerivativeBudget*‖ell‖ ≤ CF :=
    mul_le_mul_of_nonneg_left hEll (mul_nonneg (by norm_num) weakFullDerivativeBudget_nonneg)
  have hN1Full : ‖fderiv ℝ (commonSupportFullWeakEnergy a1 ha1) 0‖ ≤ CF := h1Full.trans hFirstBound
  have hN1Weak : ‖fderiv ℝ (commonSupportWeakEnergy a1 ha1) 0‖ ≤ CF := h1Weak.trans hFirstBound
  have hN1Zero : ‖fderiv ℝ (commonSupportZeroWeakEnergy a1 ha1) 0‖ ≤ CF := h1Zero.trans hFirstBound
  have hAssembly := exists_affine_commonSupport_matrix_family a1 aR ha1 haR S1 SR hS1 hSR hz1 hzR c r
  obtain ⟨a,ha,S,hS,hz,hAffine⟩ := hAssembly
  have hEqTheorem := commonSupport_weakEnergy_affine_families a a1 aR ha ha1 haR c r
    (fun θ z hzB => hAffine θ z (unitBall_subset_closedBall_two hzB))
  obtain ⟨hFullFamily,hWeakFamily,hZeroFamily⟩ := hEqTheorem
  have hD1Full := (contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0
  have hD1Weak := (contDiff_commonSupportWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0
  have hD1Zero := (contDiff_commonSupportZeroWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) 0
  have hDRFull := (contDiff_commonSupportFullWeakEnergy aR haR SR hSR hzR).differentiable (by simp) 0
  have hDRWeak := (contDiff_commonSupportWeakEnergy aR haR SR hSR hzR).differentiable (by simp) 0
  have hDRZero := (contDiff_commonSupportZeroWeakEnergy aR haR SR hSR hzR).differentiable (by simp) 0
  have hFull := affine_family_derivative_budget (P:=ℝ) (V:=BallH1 →L[ℝ] StrongDual ℝ BallH1)
    (commonSupportFullWeakEnergy a ha) (commonSupportFullWeakEnergy a1 ha1) (commonSupportFullWeakEnergy aR haR)
    (TauCeti.PDE.energyFormH1L (flatCoefficientBound c)) 0 r CF CR hFullFamily hD1Full hDRFull
    hr.le hr1 hCF hCR hN1Full hRFull
  have hWeak := affine_family_derivative_budget (P:=ℝ) (V:=BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (commonSupportWeakEnergy a ha) (commonSupportWeakEnergy a1 ha1) (commonSupportWeakEnergy aR haR)
    (nativeCoefficientWeakEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)) 0 r CF CR
    hWeakFamily hD1Weak hDRWeak hr.le hr1 hCF hCR hN1Weak hRWeak
  have hZero := affine_family_derivative_budget (P:=ℝ) (V:=BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (commonSupportZeroWeakEnergy a ha) (commonSupportZeroWeakEnergy a1 ha1) (commonSupportZeroWeakEnergy aR haR)
    (nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)) 0 r CF CR
    hZeroFamily hD1Zero hDRZero hr.le hr1 hCF hCR hN1Zero hRZero
  have hCFirst : CF ≤ C := by dsimp [C];linarith
  have hCPrincipal : CF+CR ≤ C := by dsimp [C];linarith
  have hCResidual : CR ≤ C := by dsimp [C];linarith
  refine ⟨a,ha,S,hS,hz,a1,ha1,S1,hS1,hz1,?_,hRep1,
    hZero.1.trans (mul_le_mul_of_nonneg_right hCPrincipal hr.le),
    hFull.1.trans (mul_le_mul_of_nonneg_right hCPrincipal hr.le),
    hN1Weak.trans hCFirst,hWeak.2.trans (mul_le_mul_of_nonneg_right hCResidual (sq_nonneg r)),
    hFull.2.trans (mul_le_mul_of_nonneg_right hCResidual (sq_nonneg r))⟩
  intro θ z hzB
  rw [hAffine θ z hzB,hRep1 θ z hzB,hRepR θ z hzB]
  exact (rotated_affineMatrixRemainder_identity i j
    (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r)) c r ell θ z).symm

end ShrinkingSpheres
