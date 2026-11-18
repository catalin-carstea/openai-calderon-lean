import Proof.StrongAffineOperatorPointBounds
import Proof.UniformFirstStrongTaylorData
import Proof.PoissonFirstVariationBound
import Proof.RadialEndpointCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

/-- The first Poisson variation for the scalar affine coefficient model. -/
def strongFirstPoissonVariationL (F0 F1 : SmoothCoefficientMatrix 2) (c : ℝ) :
    SphereSobolev (3/2:ℝ) →L[ℝ] BallSobolev 2 :=
  -(fixedStrongH2InclusionL.comp ((strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse.comp
    ((fullCoefficientOperatorL fixedSobolevCalculus 0 F1).comp fixedHarmonicLiftL)))

def highFirstRadialVariationL (F0 F1 : SmoothCoefficientMatrix 2) (c : ℝ) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  fixedHalfOutwardTraceL.comp (strongFirstPoissonVariationL F0 F1 c)

/-- The actual high radial endpoint has a uniform quadratic remainder after
    subtracting the genuine first variation of its scalar affine model. -/
theorem uniform_actual_high_radial_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C1 C2 : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ C1 ∧ 0 ≤ C2 ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ℓ := firstDensityCenterLinearL d y
      ∃ F F1 : SmoothCoefficientMatrix 2,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x]
          (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y r) z i j)) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => ℓ z*(1:Mat) i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        ‖highFirstRadialVariationL F0 F1 c‖ ≤ C1 ∧
        ‖actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 c‖ ≤ C2*r^2 := by
  obtain ⟨ηG,C,P,Q,F0,hηG,hC,hP,hQ,hF0,hData⟩ :=
    uniform_first_strong_taylor_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  let B := fullC1OperatorBudget fixedSobolevCalculus
  let S := strongC1OperatorBudget fixedSobolevCalculus
  let CP1 := C*(B*P)*‖fixedHarmonicLiftL‖
  let CP2 := C*(B*Q+C*(S*(Q+P))*(B*P))*‖fixedHarmonicLiftL‖
  have hB : 0 ≤ B := fullC1OperatorBudget_nonneg _
  have hS : 0 ≤ S := strongC1OperatorBudget_nonneg _
  have hCP1 : 0 ≤ CP1 := by dsimp [CP1];positivity
  have hCP2 : 0 ≤ CP2 := by dsimp [CP2];positivity
  refine ⟨min ηG 1,‖fixedHalfOutwardTraceL‖*CP1,‖fixedHalfOutwardTraceL‖*CP2,F0,
    lt_min hηG zero_lt_one,by positivity,by positivity,hF0,?_⟩
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
  have hPoint := strong_affine_operator_point_bounds fixedSobolevCalculus F F0 F1 c r P Q hP hQ hr.le hr1
    hVal1 hDeriv1 hValR hDerivR
  have hT1 : ‖T1‖ ≤ B*P := hPoint.1
  have hADiff : ‖A-A0‖ ≤ (S*(Q+P))*r := hPoint.2.1
  have hTR : ‖T-T0-r • T1‖ ≤ (B*Q)*r^2 := hPoint.2.2
  have hFlat : T0.comp fixedHarmonicLiftL = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact fullCoefficientOperator_flat_harmonicLift fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics F0 (fun x hx => hF0 x (unitBall_subset_closedBall_two hx)) c f
  have hj : ‖fixedStrongH2InclusionL‖ ≤ 1 := Submodule.norm_subtypeL_le _
  have hP1 : ‖strongFirstPoissonVariationL F0 F1 c‖ ≤ CP1 := by
    rw [strongFirstPoissonVariationL,norm_neg]
    calc
      _ ≤ ‖fixedStrongH2InclusionL‖*(‖A0.inverse‖*(‖T1‖*‖fixedHarmonicLiftL‖)) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ 1*(C*((B*P)*‖fixedHarmonicLiftL‖)) := by gcongr
      _ = _ := by dsimp [CP1];ring
  have hP2 := norm_poisson_first_variation_remainder_le fixedStrongH2InclusionL A A0 T T0 T1 fixedHarmonicLiftL
    hInv hInv0 hFlat hj r C C (S*(Q+P)) (B*P) (B*Q) hr.le hC hC (by positivity)
      (by positivity) (by positivity) hNorm hNorm0 hADiff hT1 hTR
  have hPoissonEq : fixedHarmonicLiftL-fixedStrongH2InclusionL.comp (A.inverse.comp (T.comp fixedHarmonicLiftL)) =
      strongPoissonL F := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [hPoissonEq] at hP2
  change ‖strongPoissonL F-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 F1 c‖ ≤ CP2*r^2 at hP2
  have hRadEq : actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 c =
      fixedHalfOutwardTraceL.comp (strongPoissonL F-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 F1 c) := by
    rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
    rfl
  refine ⟨F,F1,hRep,hRep1,hInv,hInv0,?_,?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left hP1 (norm_nonneg _))
  · rw [hRadEq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left hP2 (norm_nonneg _)).trans_eq (by ring))

end ShrinkingSpheres
