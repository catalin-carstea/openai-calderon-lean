import Proof.UniformRelativeRadiusHighRadialTaylorData
import Proof.CommonSupportCoefficientPointGerms
import Proof.NormalizedWeakTaylorPointData
import Proof.CommonSupportWeakConormalTaylorData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL

/-- Uniform actual weak conormal quadratic center derivative on the SAME
    normalized parallel family as the checked high-endpoint derivative. -/
theorem uniform_relative_radius_conormal_taylor_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C CN C1 CQ P Q CP1 CP2 : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ C ∧ 0 ≤ CN ∧ 0 ≤ C1 ∧ 0 ≤ CQ ∧ 0 ≤ P ∧ 0 ≤ Q ∧ 0 ≤ CP1 ∧ 0 ≤ CP2 ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A A1 D : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,∃ hD : ContDiff ℝ ∞ D,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧ (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (t,z)]
        relativeDilationFamily (normalizedFirstNormalCoefficient d y)) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (t,z)]
        relativeDilationFamily (scalarFirstCoefficient (firstDensityLogCovector d y))) ∧
      (∀ p,D p = A p-d.radius y • A1 p) ∧
      CommonSupportNativeDerivativeBounds A1 hA1 S hS hz1 C1 ∧
      CommonSupportNativeDerivativeBounds D hD S hS hzD (CQ*(d.radius y)^2) ∧
      CommonSupportNativeDerivativeBounds A hA S hS hz ((C1+CQ)*d.radius y) ∧
      CommonSupportTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 (d.radius y) F0 (CQ*(d.radius y)^2) ∧
      (∀ t ∈ V,(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 A hA S hS hz t)).IsInvertible) ∧
      ‖fderiv ℝ (fun t => actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz t)-
        d.radius y • highFirstRadialVariationL F0 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 t) 1) 0‖ ≤ C*(d.radius y)^2 ∧
      NativeWeakTaylorData (fun z => A (0,z)) (fun z => A1 (0,z)) 1 (d.radius y)
        (5*K*metricDensityBudget (4*K^2)*(4*K^2)) (K*metricDensityBudget (4*K^2)*(4*K^2)) P Q CP1 CP2 ∧
      RawAffineCoefficientBounds (fun z => A (0,z)) (fun z => A1 (0,z)) 1 (d.radius y) P Q ∧
      (∀ t ∈ V,(commonSupportZeroWeakEnergy A hA t).IsInvertible) ∧
      ‖fderiv ℝ (fun t => commonSupportWeakConormalEndpoint A hA t-(1:ℝ) • fixedLowRadialL-
        d.radius y • weakFirstConormalVariationL 1 (fun z => A1 (t,z)) (commonSupportEnergyMemLp A1 hA1 t)) 0‖ ≤
          CN*(d.radius y)^2 := by
  obtain ⟨ηH,C,C1,CQ,F0,hηH,hC,hC1,hCQ,hF0,hHigh⟩ :=
    uniform_relative_radius_high_radial_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,P,Q,CP1,CP2,hηP,hP,hQ,hCP1,hCP2,hPoint⟩ :=
    uniform_normalized_weak_taylor_point_data (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  let CW := 5*K*metricDensityBudget (4*K^2)*(4*K^2)
  let CA := K*metricDensityBudget (4*K^2)*(4*K^2)
  let CN := commonSupportConormalTaylorDerivativeBudget CW CA P Q CP1 CP2 (C1+CQ) C1 CQ
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hCW : 0 ≤ CW := by dsimp [CW,metricDensityBudget];positivity
  have hCA : 0 ≤ CA := by dsimp [CA,metricDensityBudget];positivity
  have hWB := weakFullDerivativeBudget_nonneg
  have hN := norm_nonneg fixedHarmonicH1LiftL
  have hMass : 0 ≤ sphereSurfaceMass := le_of_lt sphereSurfaceMass_pos
  have hWeakBudget : 0 ≤ commonSupportWeakTaylorDerivativeBudget CW P Q CP2 (C1+CQ) C1 CQ := by
    dsimp only [commonSupportWeakTaylorDerivativeBudget]
    positivity
  have hCN : 0 ≤ CN := by
    dsimp only [CN,commonSupportConormalTaylorDerivativeBudget]
    positivity
  refine ⟨min ηH (min ηP 1),C,CN,C1,CQ,P,Q,CP1,CP2,F0,
    lt_min hηH (lt_min hηP zero_lt_one),hC,hCN,hC1,hCQ,hP,hQ,hCP1,hCP2,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hRep,hRep1,hDField,hN1,hND,hNA,hTaylor,hInvS,hHighBound⟩ :=
    hHigh floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let r := d.radius y
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let F1 := commonSupportMatrixFamily 2 A1 hA1 S hS hz1
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hRep0 := commonSupport_coefficient_point_germs A
    (relativeDilationFamily (normalizedFirstNormalCoefficient d y)) hA S hS hz 0
    (normalizedFirstNormalCoefficient d y) (fun z hzB => hRep 0 h0V z hzB)
    (fun w => by simp only [relativeDilationFamily,add_zero,one_smul])
  have hRep10Raw := commonSupport_coefficient_point_germs A1
    (relativeDilationFamily (scalarFirstCoefficient (firstDensityLogCovector d y))) hA1 S hS hz1 0
    (scalarFirstCoefficient (firstDensityLogCovector d y)) (fun z hzB => hRep1 0 h0V z hzB)
    (fun w => by simp only [relativeDilationFamily,add_zero,one_smul])
  have hRep10 : ∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F1 0 i j) =ᶠ[𝓝 z] (fun w => firstDensityLogCovector d y w*(1:Mat) i j) := by
    simpa only [scalarFirstCoefficient_apply,Matrix.smul_apply,smul_eq_mul] using hRep10Raw
  have hPointData := hPoint floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
    d hd y hy (F 0) (F1 0) hRep0 hRep10
  simp only [F,F1,coefficientMatrixField_commonSupportMatrixFamily] at hPointData
  obtain ⟨hWeakPoint,hEntries⟩ := hPointData
  have hNA' : CommonSupportNativeDerivativeBounds A hA S hS hz ((C1+CQ)*r*1) := by simpa only [mul_one] using hNA
  have hN1' : CommonSupportNativeDerivativeBounds A1 hA1 S hS hz1 (C1*1) := by simpa only [mul_one] using hN1
  have hTaylor' : CommonSupportTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 r F0 (CQ*r^2*1) := by
    simpa only [mul_one] using hTaylor
  have hConormal := commonSupport_conormal_taylor_derivative_data A A1 hA hA1 S S hS hS hz hz1
    r CW CA P Q CP1 CP2 (C1+CQ) C1 CQ 1 hr.le hr1 hCW hCA hP hQ hCP1 hCP2
    (add_nonneg hC1 hCQ) hC1 hCQ (by norm_num) F0 hNA' hN1' hTaylor' hWeakPoint hEntries
  obtain ⟨W,hW,h0W,hInvW,hPDiff,hP1Diff,hDP1,hWeakDerivative⟩ :=
    commonSupport_weak_taylor_derivative_data A A1 hA hA1 S S hS hS hz hz1
      r CW CA P Q CP1 CP2 (C1+CQ) C1 CQ 1 hr.le hr1 hCW hP hQ hCP2
      (add_nonneg hC1 hCQ) hC1 hCQ (by norm_num) F0 hNA' hN1' hTaylor' hWeakPoint hEntries
  refine ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V ∩ W,hV.inter hW,⟨h0V,h0W⟩,
    (fun t ht => hRep t ht.1),(fun t ht => hRep1 t ht.1),
    hDField,hN1,hND,hNA,hTaylor,(fun t ht => hInvS t ht.1),hHighBound,hWeakPoint,hEntries,
    (fun t ht => hInvW t ht.2),?_⟩
  simpa only [mul_one] using hConormal

end ShrinkingSpheres
