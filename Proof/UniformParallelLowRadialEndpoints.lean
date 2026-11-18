import Proof.UniformParallelConormalTaylorData
import Proof.CommonSupportLowRadialTaylorData
import Proof.NormalizedCoefficientTaylorPointBounds
import Proof.CommonSupportLowRadialDerivativeData
import Proof.LowRadialCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse
  fullCoefficientOperatorL strongCoefficientOperatorL strongDirichletOperator
  commonSupportMatrixFamily

/-- The actual normalized parallel coefficient family has uniform quadratic
    low and high radial Taylor derivatives, with genuine local coercive,
    strong and normal inverses. The radius is held fixed in this center jet. -/
theorem uniform_parallel_low_radial_endpoints {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CH CL : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ CH ∧ 0 ≤ CL ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∃ A A1 : ℝ × X → Mat,∃ hA : ContDiff ℝ ∞ A,∃ hA1 : ContDiff ℝ ∞ A1,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ t z,z ∉ S → A (t,z) = 0,
      ∃ hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0,
      ∃ V : Set ℝ,IsOpen V ∧ (0:ℝ) ∈ V ∧ (∀ t ∈ V,y+t • a ∈ Y) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (t,z)]
        parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a (d.radius y) (frameVectorLinear d.frame y)) ∧
      (∀ t ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (t,z)]
        parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) ∧
      (∀ t ∈ V,(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 A hA S hS hz t)).IsInvertible) ∧
      (∀ t ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA t))) ∧
      (∀ t ∈ V,(negativeBoundaryCoefficientMulL
        (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz t))).IsInvertible) ∧
      ‖fderiv ℝ (fun t => actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz t)-
        d.radius y • highFirstRadialVariationL F0 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 t) 1) 0‖ ≤ CH*(d.radius y)^2*‖a‖ ∧
      DifferentiableAt ℝ (fun t => commonSupportLowRadialErrorL A hA S hS hz t-
        d.radius y • commonSupportLowFirstRadialL A1 hA1 S hS hz1 1 t) 0 ∧
      ‖fderiv ℝ (fun t => commonSupportLowRadialErrorL A hA S hS hz t-
        d.radius y • commonSupportLowFirstRadialL A1 hA1 S hS hz1 1 t) 0‖ ≤ CL*(d.radius y)^2*‖a‖ := by
  obtain ⟨ηN,C,CN,C1,CQ,P,Q,CP1,CP2,F0,hηN,hC,hCN,hC1,hCQ,hP,hQ,hCP1,hCP2,hF0,hData⟩ :=
    uniform_parallel_conormal_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,PS,QS,F0S,hηS,hPS,hQS,hF0S,hStrongPoint⟩ :=
    uniform_normalized_coefficient_taylor_point_bounds (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ
  let CA := K*metricDensityBudget (4*K^2)*(4*K^2)
  let CW := 5*K*metricDensityBudget (4*K^2)*(4*K^2)
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hCA : 0 ≤ CA := by dsimp [CA,metricDensityBudget];positivity
  obtain ⟨δ,CLow,hδ,hCLow,hLowData⟩ := exists_commonSupport_low_radial_taylor_data
    CW CA P Q CP1 CP2 PS QS CN C1 CQ hCA hP hQ hCP1 hCP2 hPS hQS hCN hC1 hCQ
  refine ⟨min ηN (min ηS (min 1 δ)),C,CLow,F0,
    lt_min hηN (lt_min hηS (lt_min zero_lt_one hδ)),hC,hCLow,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  obtain ⟨A,A1,D,hA,hA1,hD,S,hS,hz,hz1,hzD,V,hV,h0V,hVY,hRep,hRep1,hDField,hN1,hND,hNA,hTaylor,hInvS,hHigh,hPoint,hEntries,hInvW,hConormal⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy a
  let r := d.radius y
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let F1 := commonSupportMatrixFamily 2 A1 hA1 S hS hz1
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hSmall1 : ε ≤ 1 := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr1 : r ≤ 1 := hrε.trans hSmall1
  have hSmallδ : ε ≤ δ := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hrδ : r ≤ δ := hrε.trans hSmallδ
  obtain ⟨hRep0,hRep10⟩ := hd.1.parallel_coefficient_pair_point_germs hΩ (zero_lt_one.trans_le hK)
    (hd.2.1.center_mem hy) a A A1 hA hA1 S S hS hS hz hz1
    (fun z hzB => hRep 0 h0V z hzB) (fun z hzB => hRep1 0 h0V z hzB)
  obtain ⟨hVal1,hDer1,hValR,hDerR⟩ :=
    hStrongPoint floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
      d hd y hy (F 0) (F1 0) hRep0 hRep10
  have hScalar (w : UnitSphere) : coefficientMatrixField 2 (F1 0) w.val = firstDensityLogCovector d y w.val • (1:Mat) := by
    have hw2 : w.val ∈ Metric.closedBall (0:X) 2 :=
      Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)
    ext i j
    exact (hRep10 w.val hw2 i j).eq_of_nhds
  obtain ⟨W,hW,h0W,hCoercive,hNormalW,hLowDiff,hLow⟩ := hLowData A A1 hA hA1 S hS hz hz1
    r ‖a‖ hr.le hr1 hrδ (norm_nonneg a) F0 F0S hF0S (firstDensityLogCovector d y) hScalar hPoint
    hNA hN1 hTaylor hVal1 hDer1 hValR hDerR hConormal
  refine ⟨A,A1,hA,hA1,S,hS,hz,hz1,V ∩ W,hV.inter hW,⟨h0V,h0W⟩,
    (fun t ht => hVY t ht.1),(fun t ht => hRep t ht.1),(fun t ht => hRep1 t ht.1),
    (fun t ht => hInvS t ht.1),(fun t ht => hCoercive t ht.2),
    (fun t ht => hNormalW t ht.2),hHigh,hLowDiff,hLow⟩

end ShrinkingSpheres
