import Proof.UniformBoundaryRotationDerivative
import Proof.BoundaryTaylorFamilyIdentity
import Proof.RotatedFirstWeakEnergyDerivative
import Proof.FirstScalarWeakEnergyFamily
import Proof.AffineFamilyDerivativeBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Uniform actual boundary Taylor derivative budgets for the same arbitrary
    compact representatives already chosen by the conormal endpoint producer. -/
theorem uniform_actual_boundary_rotation_taylor_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ell := firstDensityCenterLinearL d y
      ∀ a : ℝ × X → Mat,∀ ha : ContDiff ℝ ∞ a,∀ S : Set X,∀ hS : IsCompact S,
      ∀ hz : ∀ θ z,z ∉ S → a (θ,z) = 0,
      ∀ a1 : ℝ × X → Mat,∀ ha1 : ContDiff ℝ ∞ a1,∀ S1 : Set X,∀ hS1 : IsCompact S1,
      ∀ hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0,
      (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = coordinateRotationPrincipalFamily i j
        (fun v : ℝ × X => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) v.2) ((θ,0),z)) →
      (∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a1 (θ,z) = ell (coordinateRotation i j θ z) • (1:Mat)) →
      let N := fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)
      let N1 := fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 θ)
      ‖fderiv ℝ N1 0‖ ≤ C ∧
      ‖fderiv ℝ (fun θ => N θ-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-r • N1 θ) 0‖ ≤ C*r^2 ∧
      (∀ k : I,‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz k θ)) 0‖ ≤ C*r^2) ∧
      ‖fderiv ℝ N 0‖ ≤ C*r ∧
      ‖fderiv ℝ (commonSupportFullWeakEnergy a1 ha1) 0‖ ≤ C := by
  have hBoundaryTheorem := uniform_actual_boundary_remainder_rotation_derivative hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,CR,hηR,hCR,hRBoundary⟩ := hBoundaryTheorem
  have hFamilyTheorem := uniform_actual_rotated_remainder_weakEnergy_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηA,CA,hηA,hCA,hAFamily⟩ := hFamilyTheorem
  let PG := K^3*|M ⟨1,by omega⟩|
  let CF := boundaryHalfDerivativeBudget*(36*(14*PG))
  let CW := 14*weakFullDerivativeBudget*PG
  let C := CF+CR+CW+1
  have hPG : 0 ≤ PG := by dsimp [PG];positivity
  have hCF : 0 ≤ CF := mul_nonneg boundaryHalfDerivativeBudget_nonneg (by positivity)
  have hCW : 0 ≤ CW := by dsimp [CW];exact mul_nonneg (mul_nonneg (by norm_num) weakFullDerivativeBudget_nonneg) hPG
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hFlatTheorem := exists_compact_flat_matrix_field
  obtain ⟨A0,hA0,hSupport0,hA0Rep⟩ := hFlatTheorem
  let a0 : ℝ × X → Mat := fun v => A0 v.2
  have ha0 : ContDiff ℝ ∞ a0 := hA0.comp contDiff_snd
  have hz0 : ∀ θ z,z ∉ tsupport A0 → a0 (θ,z) = 0 := by
    intro θ z hzS
    by_contra hn
    exact hzS (subset_closure hn)
  let F0 := commonSupportMatrixFamily 2 a0 ha0 (tsupport A0) hSupport0 hz0 0
  have hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1 := by
    intro z hzB
    change coefficientMatrixField 2 (commonSupportMatrixFamily 2 a0 ha0 (tsupport A0) hSupport0 hz0 0) z = 1
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hA0Rep z hzB
  refine ⟨min ηR (min ηA 1),C,lt_min hηR (lt_min hηA zero_lt_one),hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j
  dsimp only
  intro a ha S hS hz a1 ha1 S1 hS1 hz1 hRep hRep1
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let ell := firstDensityCenterLinearL d y
  let N := fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)
  let N1 := fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 θ)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hCenter := hd.2.1.center_mem hy
  have hLn : ‖ell‖ ≤ PG := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
    have hEn := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
    have hD := (hd.1.firstMetricDensityFactor_jet_bounds hΩ
      (zero_lt_one.trans_le hK) (by omega) hCenter).1
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hD hEn (norm_nonneg _) (by positivity)).trans_eq (by dsimp [PG];ring))
  have hFirst : ‖fderiv ℝ N1 0‖ ≤ CF :=
    (norm_fderiv_rotated_scalar_commonSupport_normal_le a1 ha1 S1 hS1 hz1 i j ell hRep1).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLn (by norm_num)) (by norm_num))
        boundaryHalfDerivativeBudget_nonneg)
  have hFullFirst : ‖fderiv ℝ (commonSupportFullWeakEnergy a1 ha1) 0‖ ≤ CW :=
    (norm_fderiv_rotated_scalar_commonSupport_fullWeakEnergy_le a1 ha1 S1 hS1 hz1 i j ell hRep1).trans
      (mul_le_mul_of_nonneg_left hLn (mul_nonneg (by norm_num) weakFullDerivativeBudget_nonneg))
  have hRPoint := hAFamily floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy i j
  obtain ⟨aR,haR,SR,hSR,hzR,hRepR,hERF,hERW,hERZ⟩ := hRPoint
  have hBoundaryR := hRBoundary floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy i j aR haR SR hSR hzR hRepR
  let NR := fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily aR haR SR hSR hzR θ)
  have hAffine (θ : ℝ) (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :
      a (θ,z) = c • (1:Mat)+r • a1 (θ,z)+aR (θ,z) := by
    rw [hRep θ z hzB,hRep1 θ z hzB,hRepR θ z hzB]
    exact rotated_affineMatrixRemainder_identity i j
      (principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r)) c r ell θ z
  have hFamilies := commonSupport_boundary_taylor_family_identity a a1 aR ha ha1 haR S S1 SR hS hS1 hSR hz hz1 hzR
    F0 c r (fun θ z => ell (coordinateRotation i j θ z)) hF0
    (fun θ w => hRep1 θ w.val (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property))) hAffine
  have hFamily (θ : ℝ) : N θ = c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))+r • N1 θ+NR θ := by
    have h := congrFun hFamilies.1 θ
    change N θ-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-r • N1 θ = NR θ at h
    rw [← h]
    module
  have hN1Diff := (contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a1 ha1 S1 hS1 hz1).differentiable (by simp) 0
  have hNRDiff := (contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace aR haR SR hSR hzR).differentiable (by simp) 0
  have hBudget := affine_family_derivative_budget N N1 NR
    (c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) 0 r CF CR hFamily hN1Diff hNRDiff
    hr.le hr1 hCF hCR hFirst hBoundaryR.1
  have hCFirst : CF ≤ C := by dsimp [C];linarith
  have hCRem : CR ≤ C := by dsimp [C];linarith
  have hCFull : CW ≤ C := by dsimp [C];linarith
  have hCPrincipal : CF+CR ≤ C := by dsimp [C];linarith
  refine ⟨hFirst.trans hCFirst,hBudget.2.trans (mul_le_mul_of_nonneg_right hCRem (sq_nonneg r)),?_,
    hBudget.1.trans (mul_le_mul_of_nonneg_right hCPrincipal hr.le),hFullFirst.trans hCFull⟩
  intro k
  have hNormEq := congrArg (fun f : ℝ → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    ‖fderiv ℝ f 0‖) (hFamilies.2 k)
  exact hNormEq.le.trans ((hBoundaryR.2 k).trans (mul_le_mul_of_nonneg_right hCRem (sq_nonneg r)))

end ShrinkingSpheres
