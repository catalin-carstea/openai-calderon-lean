import Proof.CoerciveNeighborhood
import Proof.CommonSupportTaylorDerivativeData
import Proof.LocalLowRadialTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The native principal/first/residual derivative data and conormal bound
    supply the true local low-radial quadratic derivative. The actual coercive
    and normal inverse neighborhoods are constructed, not assumed. -/
theorem commonSupport_low_radial_derivative_data
    (a a1 : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r C1 CQ CP CD L : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCP : 0 ≤ CP) (hCD : 0 ≤ CD) (hL : 0 ≤ L) (F0 : SmoothCoefficientMatrix 2)
    (hNative : CommonSupportNativeDerivativeBounds a ha S hS hz ((C1+CQ)*r*L))
    (hNative1 : CommonSupportNativeDerivativeBounds a1 ha1 S1 hS1 hz1 (C1*L))
    (hTaylor : CommonSupportTaylorDerivativeBounds a a1 ha ha1 S S1 hS hS1 hz hz1 r F0 (CQ*r^2*L))
    (hCD1 : boundaryHalfDerivativeBudget*(36*C1) ≤ CD)
    (hCDQ : boundaryHalfDerivativeBudget*(36*CQ) ≤ CD)
    (hCDT : boundaryHalfDerivativeBudget*(78*CQ) ≤ CD)
    (hCDM : boundaryHalfDerivativeBudget*(36*(C1+CQ)) ≤ CD)
    (hCDE : weakFullDerivativeBudget*C1 ≤ CD)
    (hCoercive : IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha 0)))
    (hNormal0 : (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz 0)).IsInvertible)
    (hMINorm : ‖(negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz 0)).inverse‖ ≤ CP)
    (hMDiff : ‖negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz 0)-
      (1:ℝ) • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ CP*r)
    (hBPoint : ‖commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1 0‖ ≤ CP)
    (hJPoint : ‖commonSupportLowRadialErrorL a ha S hS hz 0-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1 0‖ ≤ CP*r^2)
    (hDN : ‖fderiv ℝ (fun t => commonSupportWeakConormalEndpoint a ha t-(1:ℝ) • fixedLowRadialL-
      r • weakFirstConormalVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) 0‖ ≤ CD*r^2*L) :
    ∃ U : Set ℝ,IsOpen U ∧ (0:ℝ) ∈ U ∧
      (∀ t ∈ U,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha t))) ∧
      (∀ t ∈ U,(negativeBoundaryCoefficientMulL
        (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t))).IsInvertible) ∧
      DifferentiableAt ℝ (fun t => commonSupportLowRadialErrorL a ha S hS hz t-
        r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1 t) 0 ∧
      ‖fderiv ℝ (fun t => commonSupportLowRadialErrorL a ha S hS hz t-
        r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1 t) 0‖ ≤
          lowRadialAngleDerivativeBudget 1 CP CD*r^2*L := by
  obtain ⟨W,hW,h0W,hCoerciveW⟩ := exists_commonSupport_coercive_neighborhood a ha S hS hz hCoercive
  let M := fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz t)
  have hMSmooth : ContDiff ℝ ∞ M := contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a ha S hS hz
  let U := W ∩ {t : ℝ | (M t).IsInvertible}
  have hU : IsOpen U := hW.inter (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hMSmooth.continuous)
  have h0U : (0:ℝ) ∈ U := ⟨h0W,hNormal0⟩
  have hCoerciveU : ∀ t ∈ U,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha t)) :=
    fun t ht => hCoerciveW t ht.1
  have hWeak : ∀ t ∈ U,(commonSupportZeroWeakEnergy a ha t).IsInvertible :=
    fun t ht => isInvertible_of_bilinear_coercive _ (hCoerciveU t ht)
  have hNormal : ∀ t ∈ U,(negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz t))).IsInvertible := by
    intro t ht
    rw [← commonSupport_negative_normal_multiplier_eq]
    exact ht.2
  have hDM1 : ‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 t)) 0‖ ≤ CD*L :=
    by nlinarith only [hNative1.normal,mul_le_mul_of_nonneg_right hCD1 hL]
  have hDMQ : ‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz t)-
      (1:ℝ) • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
      r • negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 t)) 0‖ ≤ (CD*L)*r^2 := by
    have hBound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCDQ hL) (sq_nonneg r)
    have hRaw := hTaylor.normal
    simp only [one_smul] at *
    nlinarith only [hRaw,hBound]
  have hDT (j : I) : ‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t)) 0‖ ≤ (CD*L)*r^2 :=
    by
      have hBound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCDT hL) (sq_nonneg r)
      nlinarith only [hTaylor.tangent j,hBound]
  have hDM : ‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz t)) 0‖ ≤ (CD*L)*r :=
    by nlinarith only [hNative.normal,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCDM hL) hr]
  have hDE1 : ‖fderiv ℝ (commonSupportFullWeakEnergy a1 ha1) 0‖ ≤ CD*L :=
    by nlinarith only [hNative1.fullWeak,mul_le_mul_of_nonneg_right hCDE hL]
  have hDN' : ‖fderiv ℝ (fun t => commonSupportWeakConormalEndpoint a ha t-(1:ℝ) • fixedLowRadialL-
      r • weakFirstConormalVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) 0‖ ≤ (CD*L)*r^2 :=
    hDN.trans_eq (by ring)
  obtain ⟨hDiff,hBound⟩ := norm_commonSupportLowRadial_first_remainder_derivative_le_local
    a a1 ha ha1 S S1 hS hS1 hz hz1 1 r 1 CP (CD*L) 0 U hU h0U (by norm_num) hr hr1
    (by norm_num) hCP (mul_nonneg hCD hL) (by norm_num) hWeak hNormal
    hMINorm hMDiff hBPoint hJPoint hDN' hDM1 hDMQ hDT hDM hDE1
  refine ⟨U,hU,h0U,hCoerciveU,hNormal,hDiff,hBound.trans_eq ?_⟩
  dsimp only [lowRadialAngleDerivativeBudget]
  ring

end ShrinkingSpheres
