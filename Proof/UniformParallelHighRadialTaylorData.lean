import Proof.UniformParallelNativeTaylorData
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
theorem uniform_parallel_high_radial_taylor_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C C1 CQ : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ C ∧ 0 ≤ C1 ∧ 0 ≤ CQ ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∃ A A1 D : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,∃ hD : ContDiff ℝ ∞ D,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧ (∀ t ∈ V,y+t • a ∈ Y) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (t,z)]
        parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a (d.radius y) (frameVectorLinear d.frame y)) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (t,z)]
        parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) ∧
      (∀ p,D p = A p-d.radius y • A1 p) ∧
      CommonSupportNativeDerivativeBounds A1 hA1 S hS hz1 (C1*‖a‖) ∧
      CommonSupportNativeDerivativeBounds D hD S hS hzD (CQ*(d.radius y)^2*‖a‖) ∧
      CommonSupportNativeDerivativeBounds A hA S hS hz ((C1+CQ)*d.radius y*‖a‖) ∧
      CommonSupportTaylorDerivativeBounds A A1 hA hA1 S S hS hS hz hz1 (d.radius y) F0 (CQ*(d.radius y)^2*‖a‖) ∧
      (∀ t ∈ V,(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 A hA S hS hz t)).IsInvertible) ∧
      ‖fderiv ℝ (fun t => actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz t)-
        d.radius y • highFirstRadialVariationL F0 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 t) 1) 0‖ ≤ C*(d.radius y)^2*‖a‖ := by
  obtain ⟨ηD,C1,CQ,hηD,hC1,hCQ,hData⟩ := uniform_parallel_native_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,CI,P,Q,F0,hηP,hCI,hP,hQ,hF0,hPoint⟩ :=
    uniform_normalized_strong_taylor_point_data (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  let C := commonSupportHighRadialDerivativeBudget CI P Q C1 CQ
  have hC : 0 ≤ C := commonSupportHighRadialDerivativeBudget_nonneg CI P Q C1 CQ hCI hP hQ hC1 hCQ
  refine ⟨min ηD (min ηP 1),C,C1,CQ,F0,lt_min hηD (lt_min hηP zero_lt_one),hC,hC1,hCQ,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hDField,hN1,hND,hNA,hTaylor⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy a
  let r := d.radius y
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let F1 := commonSupportMatrixFamily 2 A1 hA1 S hS hz1
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hRep0,hRep10⟩ := hd.1.parallel_coefficient_pair_point_germs hΩ (zero_lt_one.trans_le hK)
    (hd.2.1.center_mem hy) a A A1 hA hA1 S S hS hS hz hz1
    (fun z hzB => hRep 0 h0V z hzB) (fun z hzB => hRep1 0 h0V z hzB)
  obtain ⟨hInvPoint,hInvNorm,hInvBase,hBaseNorm,hVal1,hDer1,hValR,hDerR⟩ :=
    hPoint floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy (F 0) (F1 0) hRep0 hRep10
  obtain ⟨W,hW,h0W,hInv,hHigh⟩ := commonSupport_high_radial_taylor_derivative_data A A1 hA hA1 S hS hz hz1
    r CI P Q C1 CQ ‖a‖ hr.le hr1 hCI hP hQ hC1 hCQ (norm_nonneg a) F0 hF0
    hNA hN1 (hTaylor F0) hInvPoint hInvNorm hInvBase hBaseNorm hVal1 hDer1 hValR hDerR
  refine ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V ∩ W,hV.inter hW,⟨h0V,h0W⟩,
    (fun t ht => hVY t ht.1),(fun t ht => hRep t ht.1),(fun t ht => hRep1 t ht.1),
    hDField,hN1,hND,hNA,hTaylor F0,(fun t ht => hInv t ht.2),hHigh⟩

end ShrinkingSpheres
