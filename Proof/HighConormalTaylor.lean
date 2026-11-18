import Proof.HalfConormalCoefficient
import Proof.StrongPoissonTaylorBounds
import Proof.WeakEnergyAffineTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

def actualHighConormalL (F : SmoothCoefficientMatrix 2) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (halfConormalCoefficientL F).comp (strongPoissonL F)

def highConormalFlatL (c : ℝ) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  c • fixedHalfOutwardTraceL.comp fixedHarmonicLiftL

def highFirstConormalVariationL (F0 F1 : SmoothCoefficientMatrix 2) (c : ℝ) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (halfConormalCoefficientL (c • F0)).comp (strongFirstPoissonVariationL F0 F1 c)+
    (halfConormalCoefficientL F1).comp fixedHarmonicLiftL

/-- The high conormal remainder is quadratic with common constants, using
    local C1 coefficient control and the actual strong Dirichlet inverses. -/
theorem uniform_actual_high_conormal_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CH : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ CH ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let ell := firstDensityCenterLinearL d y
      ∃ F F1 : SmoothCoefficientMatrix 2,
      ∃ ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 x) 0 0) ⊤
        ((volume:Measure X).restrict ballOpens),
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => ell z*(1:Mat) i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        ‖actualHighConormalL F-highConormalFlatL c-
          d.radius y • highFirstConormalVariationL F0 F1 c‖ ≤ CH*(d.radius y)^2 := by
  obtain ⟨ηG,C,P,Q,F0,hηG,hC,hP,hQ,hF0,hData⟩ :=
    uniform_first_strong_taylor_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  let BT := fullC1OperatorBudget fixedSobolevCalculus
  let BS := strongC1OperatorBudget fixedSobolevCalculus
  let G := halfConormalC1Budget
  let CP1 := C*(BT*P)*‖fixedHarmonicLiftL‖
  let CP2 := C*(BT*Q+C*(BS*P+BS*Q)*(BT*P))*‖fixedHarmonicLiftL‖
  let DA := K*‖fixedHalfOutwardTraceL‖+G*P+G*Q
  let CH := DA*CP2+(G*P+G*Q)*CP1+G*Q*‖fixedHarmonicLiftL‖
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hBT : 0 ≤ BT := fullC1OperatorBudget_nonneg _
  have hBS : 0 ≤ BS := strongC1OperatorBudget_nonneg _
  have hG : 0 ≤ G := halfConormalC1Budget_nonneg
  have hCP1 : 0 ≤ CP1 := by
    change 0 ≤ C*(BT*P)*‖fixedHarmonicLiftL‖
    positivity
  have hCP2 : 0 ≤ CP2 := by
    change 0 ≤ C*(BT*Q+C*(BS*P+BS*Q)*(BT*P))*‖fixedHarmonicLiftL‖
    positivity
  have hDA : 0 ≤ DA := by
    change 0 ≤ K*‖fixedHalfOutwardTraceL‖+G*P+G*Q
    positivity
  have hCH : 0 ≤ CH := by
    change 0 ≤ DA*CP2+(G*P+G*Q)*CP1+G*Q*‖fixedHarmonicLiftL‖
    positivity
  refine ⟨min ηG 1,CH,F0,lt_min hηG zero_lt_one,hCH,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  obtain ⟨F,F1,hRep,hRep1,hInv,hNorm,hInv0,hNorm0,hVal1,hDeriv1,hValR,hDerivR⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let r := d.radius y
  let R := F-c • F0-r • F1
  let AS := strongDirichletOperator fixedSobolevCalculus 0 F
  let AS0 := strongDirichletOperator fixedSobolevCalculus 0 (c • F0)
  let AS1 := strongDirichletOperator fixedSobolevCalculus 0 F1
  let T := fullCoefficientOperatorL fixedSobolevCalculus 0 F
  let T0 := fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)
  let T1 := fullCoefficientOperatorL fixedSobolevCalculus 0 F1
  let A := halfConormalCoefficientL F
  let A0 := halfConormalCoefficientL (c • F0)
  let A1 := halfConormalCoefficientL F1
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans (min_le_right _ _))
  have hqr : 0 ≤ Q*r^2 := mul_nonneg hQ (sq_nonneg _)
  have hT1 : ‖T1‖ ≤ BT*P := norm_fullCoefficientOperator_zero_le fixedSobolevCalculus F1 P hP hVal1 hDeriv1
  have hAS1 : ‖AS1‖ ≤ BS*P := norm_strongDirichletOperator_zero_le fixedSobolevCalculus F1 P hP hVal1 hDeriv1
  have hTR : ‖T-T0-r • T1‖ ≤ (BT*Q)*r^2 := by
    have hEq : T-T0-r • T1 = fullCoefficientOperatorL fixedSobolevCalculus 0 R := by
      dsimp only [T,T0,T1,R]
      simp only [(fullCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
        (fullCoefficientOperatorL fixedSobolevCalculus 0).map_smul]
    exact (congrArg norm hEq).le.trans
      ((norm_fullCoefficientOperator_zero_le fixedSobolevCalculus R (Q*r^2) hqr hValR hDerivR).trans_eq (by ring))
  have hASR : ‖AS-AS0-r • AS1‖ ≤ (BS*Q)*r^2 := by
    have hEq : AS-AS0-r • AS1 = strongDirichletOperator fixedSobolevCalculus 0 R := by
      change (strongCoefficientOperatorL fixedSobolevCalculus 0) F-
        (strongCoefficientOperatorL fixedSobolevCalculus 0) (c • F0)-
        r • (strongCoefficientOperatorL fixedSobolevCalculus 0) F1 =
        (strongCoefficientOperatorL fixedSobolevCalculus 0) (F-c • F0-r • F1)
      simp only [(strongCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
        (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul]
    exact (congrArg norm hEq).le.trans
      ((norm_strongDirichletOperator_zero_le fixedSobolevCalculus R (Q*r^2) hqr hValR hDerivR).trans_eq (by ring))
  have hASDiff : ‖AS-AS0‖ ≤ (BS*P+BS*Q)*r :=
    norm_sub_of_affine_remainder_le AS AS0 AS1 r (BS*P) (BS*Q) hr.le hr1 (by positivity) (by positivity) hAS1 hASR
  have hP1 : ‖strongFirstPoissonVariationL F0 F1 c‖ ≤ CP1 :=
    norm_strongFirstPoissonVariationL_le F0 F1 c C (BT*P) hC (by positivity) hNorm0 hT1
  have hPR : ‖strongPoissonL F-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 F1 c‖ ≤ CP2*r^2 :=
    norm_strongPoisson_first_remainder_le F F0 F1 c r C C (BS*P+BS*Q) (BT*P) (BT*Q)
      hr.le hC hC (by positivity) (by positivity) (by positivity)
      (fun x hx => hF0 x (unitBall_subset_closedBall_two hx)) hInv hInv0 hNorm hNorm0 hASDiff hT1 hTR
  have hA1 : ‖A1‖ ≤ G*P := norm_halfConormalCoefficientL_local_C1 F1 P hP hVal1 hDeriv1
  have hAR : ‖A-A0-r • A1‖ ≤ (G*Q)*r^2 := by
    have hEq : A-A0-r • A1 = halfConormalCoefficientL R := by
      dsimp only [A,A0,A1,R]
      simp only [halfConormalCoefficientL.map_sub,halfConormalCoefficientL.map_smul]
    exact (congrArg norm hEq).le.trans
      ((norm_halfConormalCoefficientL_local_C1 R (Q*r^2) hqr hValR hDerivR).trans_eq (by ring))
  have hADiff : ‖A-A0‖ ≤ (G*P+G*Q)*r :=
    norm_sub_of_affine_remainder_le A A0 A1 r (G*P) (G*Q) hr.le hr1 (by positivity) (by positivity) hA1 hAR
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hcK : |c| ≤ K := by
    rw [abs_of_pos hc]
    exact hd.1.firstMetricDensityFactor_le hKpos (hd.2.1.center_mem hy)
  have hA0Eq := halfConormalCoefficientL_flat F0 c (fun x hx => hF0 x (unitBall_subset_closedBall_two hx))
  have hA0Norm : ‖A0‖ ≤ K*‖fixedHalfOutwardTraceL‖ :=
    (congrArg (fun S : BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) => ‖S‖) hA0Eq).le.trans
      (by rw [norm_smul,Real.norm_eq_abs];exact mul_le_mul_of_nonneg_right hcK (norm_nonneg _))
  have hANorm : ‖A‖ ≤ DA := by
    have hEq : A = (A-A0)+A0 := by abel
    calc
      _ ≤ ‖A-A0‖+‖A0‖ := (congrArg norm hEq).le.trans (norm_add_le _ _)
      _ ≤ (G*P+G*Q)*r+K*‖fixedHalfOutwardTraceL‖ := add_le_add hADiff hA0Norm
      _ ≤ (G*P+G*Q)*1+K*‖fixedHalfOutwardTraceL‖ := by gcongr
      _ = DA := by dsimp only [DA];ring
  have hb := norm_operator_poisson_taylor_le A A0 A1 (strongPoissonL F) fixedHarmonicLiftL
    (strongFirstPoissonVariationL F0 F1 c) r DA (G*P) (G*Q) CP1 CP2
    hr.le hDA (by positivity) (by positivity) hCP1 hCP2 hANorm hADiff hAR hPR hP1
  have hFlat : A0.comp fixedHarmonicLiftL = highConormalFlatL c := by
    have h := congrArg (fun S : BallSobolev 2 →L[ℝ] SphereSobolev (1/2:ℝ) => S.comp fixedHarmonicLiftL) hA0Eq
    simpa only [ContinuousLinearMap.smul_comp,highConormalFlatL] using h
  have hEq := congrArg (fun S : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) =>
    A.comp (strongPoissonL F)-S-r • highFirstConormalVariationL F0 F1 c) hFlat
  have hn := congrArg (fun S : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => ‖S‖) hEq
  refine ⟨F,F1,memLp_coefficient_energy_of_entry_bound F1 P hP hVal1,hRep,hRep1,hInv,hInv0,?_⟩
  exact hn ▸ hb

end ShrinkingSpheres
