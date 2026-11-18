import Proof.NormalFrameRelativeActualCoefficientGerms
import Proof.NormalizedWeakTaylorPointData
import Proof.NormalizedLowRadialPointData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

structure NormalFrameRelativeNativePointData {Y Ω : Set X} {d : Data} {y : X}
    {N : ℕ} {Z C : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C)
    (F0 : SmoothCoefficientMatrix 2) (CI CW : ℝ) : Prop where
  strong : (strongDirichletOperator fixedSobolevCalculus 0
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported ((y,frameVectorLinear d.frame y),0))).IsInvertible
  strongNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported ((y,frameVectorLinear d.frame y),0))).inverse‖ ≤ CI
  flatStrong : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible
  flatStrongNorm : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ CI
  weak : (commonSupportZeroWeakEnergy q.a q.smooth ((y,frameVectorLinear d.frame y),0)).IsInvertible
  weakNorm : ‖(commonSupportZeroWeakEnergy q.a q.smooth ((y,frameVectorLinear d.frame y),0)).inverse‖ ≤ CW
  normal : (negativeBoundaryCoefficientMulL
    (normalCoefficientJetsFamily q.a q.smooth q.support q.compact q.supported ((y,frameVectorLinear d.frame y),0))).IsInvertible
  normalNorm : ‖(negativeBoundaryCoefficientMulL
    (normalCoefficientJetsFamily q.a q.smooth q.support q.compact q.supported ((y,frameVectorLinear d.frame y),0))).inverse‖ ≤ 2
  coercive : IsCoercive (TauCeti.PDE.energyFormH1L0
    (commonSupportEnergyMemLp q.a q.smooth ((y,frameVectorLinear d.frame y),0)))

/-- Existing actual normalized point estimates apply to every representative
    in the new genuine relative family. The same inverse witnesses are kept. -/
theorem uniform_normalFrameRelative_native_point_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CI CW : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ η ≤ 1 ∧ 0 ≤ CI ∧ 0 ≤ CW ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ N : ℕ,∀ Z C : ℝ,2 ≤ Z →
      ∀ q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
        (frameVectorLinear d.frame y) (d.radius y) N Z C,
      NormalFrameRelativeNativePointData q F0 CI CW := by
  obtain ⟨ηS,CI,P,Q,F0,hηS,hCI,hP,hQ,hF0,hStrong⟩ :=
    uniform_normalized_strong_taylor_point_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,Pw,Qw,CP1,CP2,hηW,hPw,hQw,hCP1,hCP2,hWeak⟩ :=
    uniform_normalized_weak_taylor_point_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  let CW := 5*K*metricDensityBudget (4*K^2)*(4*K^2)
  let CA := K*metricDensityBudget (4*K^2)*(4*K^2)
  let D := boundaryHalfMultiplierBudget*36*Q+boundaryHalfMultiplierBudget*36*P
  have hMult := boundaryHalfMultiplierBudget_nonneg
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hCW : 0 ≤ CW := by dsimp only [CW,metricDensityBudget];positivity
  have hCA : 0 ≤ CA := by dsimp only [CA,metricDensityBudget];positivity
  have hD : 0 ≤ D := by dsimp only [D];positivity
  have hDen : 0 < 2*(D+1) := by positivity
  refine ⟨min ηS (min ηW (min 1 (2*(D+1))⁻¹)),CI,CW,F0,
    lt_min hηS (lt_min hηW (lt_min zero_lt_one (inv_pos.mpr hDen))),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),hCI,hCW,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy N Z C hZ q
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p0
  let F1 := commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported p0
  let r := d.radius y
  have hSmallS := hSmall.trans (min_le_left _ _)
  have hSmallW := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨hRep,hRep1⟩ := q.actual_point_germs hΩ hd.1 (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy) hZ
  obtain ⟨hInv,hNI,hInv0,hNI0,hVal1,hDer1,hValR,hDerR⟩ := hStrong floor hf ε hε hSmallS d hd y hy F F1 hRep hRep1
  obtain ⟨t,hEntries⟩ := hWeak floor hf ε hε hSmallW d hd y hy F F1 hRep hRep1
  have tRaw : NativeWeakTaylorData (fun z => q.a (p0,z)) (fun z => q.a1 (p0,z)) 1 r CW CA Pw Qw CP1 CP2 :=
    by simpa only [F,F1,coefficientMatrixField_commonSupportMatrixFamily] using t
  have hWInv : (commonSupportZeroWeakEnergy q.a q.smooth p0).IsInvertible :=
    nativeZeroCoefficientEnergy_isInvertible (commonSupportEnergyMemLp q.a q.smooth p0) tRaw.energy.coercive
  have hWNI : ‖(commonSupportZeroWeakEnergy q.a q.smooth p0).inverse‖ ≤ CW := by
    change ‖(nativeZeroCoefficientEnergyL (fun z => q.a (p0,z)) 0 0 (commonSupportEnergyMemLp q.a q.smooth p0)).inverse‖ ≤ CW
    rw [nativeZeroCoefficientEnergy_inverse_eq]
    exact tRaw.energy.inverse_bound
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hrSmall : r ≤ (2*(D+1))⁻¹ :=
    hrε.trans (hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hDr : D*r ≤ (1/2:ℝ) := by
    calc
      _ ≤ D*(2*(D+1))⁻¹ := mul_le_mul_of_nonneg_left hrSmall hD
      _ = D/(2*(D+1)) := by rw [div_eq_mul_inv]
      _ ≤ (1/2:ℝ) := (div_le_iff₀ hDen).mpr (by nlinarith only [hD])
  have hScalar (w : UnitSphere) : coefficientMatrixField 2 F1 w.val =
      firstDensityLogCovector d y w.val • (1:Mat) := by
    have hw : w.val ∈ Metric.closedBall (0:X) 2 := by
      simpa only [Metric.mem_closedBall,dist_zero_right,mem_sphere_zero_iff_norm.mp w.property] using
        (show (1:ℝ) ≤ 2 by norm_num)
    ext i j
    exact (hRep1 w.val hw i j).eq_of_nhds
  have hValR' := hValR
  have hDerR' := hDerR
  rw [← one_smul ℝ F0] at hValR' hDerR'
  obtain ⟨hNormal,hNormalNorm,hNear,hFirst,hRest⟩ := normalized_low_radial_point_data F F0 F1 r CW CA Pw Qw CP1 CP2 P Q
    hr.le hr1 hCA hPw hQw hCP1 hCP2 hP hQ t hF0 (firstDensityLogCovector d y) hScalar
    hVal1 hDer1 hValR' hDerR' hDr
  have hNormalEq := commonSupport_negative_normal_multiplier_eq q.a q.smooth q.support q.compact q.supported p0
  rw [← hNormalEq] at hNormal hNormalNorm
  exact ⟨hInv,hNI,hInv0,hNI0,hWInv,hWNI,hNormal,hNormalNorm,tRaw.energy.coercive⟩

end ShrinkingSpheres
