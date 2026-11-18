import Proof.UniformRelativeRadiusNativeTaylorData
import Proof.CommonSupportCoefficientPointGerms
import Proof.NormalizedStrongTaylorPointData
import Proof.ParallelCoefficientPointGerms
import Proof.StrongAffineOperatorPointBounds
import Proof.CommonSupportHighRadialTaylorData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL

/-- Actual uniform quadratic derivative of the normalized high radial Taylor
    remainder along a parallel center path, with the same genuine coefficients
    and canonical first model. The admitted radius is frozen for this derivative. -/
theorem uniform_relative_radius_high_radial_taylor_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C C1 CQ : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ C ∧ 0 ≤ C1 ∧ 0 ≤ CQ ∧
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
        d.radius y • highFirstRadialVariationL F0 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 t) 1) 0‖ ≤ C*(d.radius y)^2 := by
  obtain ⟨ηD,C1,CQ,hηD,hC1,hCQ,hData⟩ := uniform_relative_radius_native_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,CI,P,Q,F0,hηP,hCI,hP,hQ,hF0,hPoint⟩ :=
    uniform_normalized_strong_taylor_point_data (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  let C := commonSupportHighRadialDerivativeBudget CI P Q C1 CQ
  have hC : 0 ≤ C := commonSupportHighRadialDerivativeBudget_nonneg CI P Q C1 CQ hCI hP hQ hC1 hCQ
  refine ⟨min ηD (min ηP 1),C,C1,CQ,F0,lt_min hηD (lt_min hηP zero_lt_one),hC,hC1,hCQ,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hRep,hRep1,hDField,hN1,hND,hNA,hTaylor⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
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
  obtain ⟨hInvPoint,hInvNorm,hInvBase,hBaseNorm,hVal1,hDer1,hValR,hDerR⟩ :=
    hPoint floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy (F 0) (F1 0) hRep0 hRep10
  obtain ⟨W,hW,h0W,hInv,hHigh⟩ := commonSupport_high_radial_taylor_derivative_data A A1 hA hA1 S hS hz hz1
    r CI P Q C1 CQ 1 hr.le hr1 hCI hP hQ hC1 hCQ (by norm_num) F0 hF0
    (by simpa only [mul_one] using hNA) (by simpa only [mul_one] using hN1)
    (by simpa only [mul_one] using hTaylor F0) hInvPoint hInvNorm hInvBase hBaseNorm hVal1 hDer1 hValR hDerR
  refine ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V ∩ W,hV.inter hW,⟨h0V,h0W⟩,
    (fun t ht => hRep t ht.1),(fun t ht => hRep1 t ht.1),
    hDField,hN1,hND,hNA,hTaylor F0,(fun t ht => hInv t ht.2),?_⟩
  simpa only [mul_one] using hHigh

end ShrinkingSpheres
