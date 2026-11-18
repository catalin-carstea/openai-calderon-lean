import Proof.LowRadialDerivativeBudget
import Proof.CommonSupportRadialTaylorIdentity
import Proof.LowRadialTaylorDerivative

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
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The actual native conormal, normal/tangent and first-variation bounds
    give a quadratic derivative of the same actual low radial Taylor remainder. -/
theorem norm_commonSupportLowRadial_first_remainder_derivative_le_local
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0)
    (c r C0 CP CD : ℝ) (x : P) (V : Set P) (hV : IsOpen V) (hx : x ∈ V) (hc : c ≠ 0) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hC0 : 0 ≤ C0) (hCP : 0 ≤ CP) (hCD : 0 ≤ CD) (hci : |c⁻¹| ≤ C0)
    (hWeak : ∀ θ ∈ V,(commonSupportZeroWeakEnergy a ha θ).IsInvertible)
    (hNormal : ∀ θ ∈ V,(negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz θ))).IsInvertible)
    (hMINorm : ‖(negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz x)).inverse‖ ≤ CP)
    (hMDiff : ‖negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz x)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))‖ ≤ CP*r)
    (hBPoint : ‖commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c x‖ ≤ CP)
    (hJPoint : ‖commonSupportLowRadialErrorL a ha S hS hz x-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c x‖ ≤ CP*r^2)
    (hDN : ‖fderiv ℝ (fun θ => commonSupportWeakConormalEndpoint a ha θ-c • fixedLowRadialL-
      r • weakFirstConormalVariationL c (fun z => a1 (θ,z)) (commonSupportEnergyMemLp a1 ha1 θ)) x‖ ≤ CD*r^2)
    (hDM1 : ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 θ)) x‖ ≤ CD)
    (hDMQ : ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
      r • negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 θ)) x‖ ≤ CD*r^2)
    (hDT : ∀ j : I,‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j θ)) x‖ ≤ CD*r^2)
    (hDM : ‖fderiv ℝ (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)) x‖ ≤ CD*r)
    (hDE1 : ‖fderiv ℝ (commonSupportFullWeakEnergy a1 ha1) x‖ ≤ CD) :
    DifferentiableAt ℝ (fun θ => commonSupportLowRadialErrorL a ha S hS hz θ-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ) x ∧
    ‖fderiv ℝ (fun θ => commonSupportLowRadialErrorL a ha S hS hz θ-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c θ) x‖ ≤
        lowRadialAngleDerivativeBudget C0 CP CD*r^2 := by
  let N := commonSupportWeakConormalEndpoint a ha
  let N1 := fun θ => weakFirstConormalVariationL c (fun z => a1 (θ,z)) (commonSupportEnergyMemLp a1 ha1 θ)
  let M := fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)
  let M1 := fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 θ)
  let T := fun j θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j θ)
  let B := commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 c
  let J := fun θ => commonSupportLowRadialErrorL a ha S hS hz θ-r • B θ
  let NQ := fun θ => N θ-c • fixedLowRadialL-r • N1 θ
  let MQ := fun θ => M θ-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-r • M1 θ
  let DB := C0*(sphereSurfaceMass⁻¹*‖fixedHarmonicH1LiftL‖^2*CD+CD*‖fixedLowRadialL‖)
  let DR := CD+CD*‖fixedLowRadialL‖+CD*∑ j : I,‖fixedSphereTangentialL j‖+CD*CP+CP*DB
  let R := fun θ => NQ θ-(MQ θ).comp fixedLowRadialL-∑ j : I,(T j θ).comp (fixedSphereTangentialL j)-
    r • (M θ-c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))).comp (B θ)
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hDB : 0 ≤ DB := by dsimp [DB];positivity
  have hDR : 0 ≤ DR := by dsimp [DR];positivity
  have hN0 : DifferentiableAt ℝ N x :=
    ((contDiffOn_commonSupportWeakConormalEndpoint a ha S hS hz V hWeak).contDiffAt
      (hV.mem_nhds hx)).differentiableAt (by simp)
  have hE1 := (contDiff_commonSupportFullWeakEnergy a1 ha1 S1 hS1 hz1).differentiable (by simp) x
  have hN1Theorem := commonSupport_weakFirstConormal_coefficient_derivative a1 ha1 c x hE1 CD hCD hDE1
  obtain ⟨hN1Diff,hDN1⟩ := hN1Theorem
  have hM0 := (contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a ha S hS hz).differentiable (by simp) x
  have hM10 := (contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a1 ha1 S1 hS1 hz1).differentiable (by simp) x
  have hT0 (j : I) := (contDiff_negativeHalf_tangentCoefficientFamily fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a ha S hS hz j).differentiable (by simp) x
  have hBTheorem := commonSupport_lowFirstRadial_derivative a1 ha1 S1 hS1 hz1 c x
    C0 CD CD hC0 hCD hCD hci hDE1 hDM1
  obtain ⟨hB0,hDB0⟩ := hBTheorem
  have hL0 := ((contDiffOn_commonSupportLowRadialErrorL a ha S hS hz V hWeak hNormal).contDiffAt
    (hV.mem_nhds hx)).differentiableAt (by simp)
  have hJ0 : DifferentiableAt ℝ J x := hL0.sub (hB0.const_smul r)
  have hNQ0 : DifferentiableAt ℝ NQ x :=
    (hN0.sub_const _).sub (hN1Diff.const_smul r)
  have hMQ0 : DifferentiableAt ℝ MQ x := (hM0.sub_const _).sub (hM10.const_smul r)
  have hRNorm : ‖fderiv ℝ R x‖ ≤ DR*r^2 :=
    norm_radial_taylor_rhs_derivative_le (P:=P) (E:=SphereSobolev (1/2:ℝ)) (F:=SphereSobolev (-(1/2:ℝ)))
      NQ B MQ M T fixedLowRadialL fixedSphereTangentialL x c r CD CD CD CD CP CP DB
      hNQ0 hB0 hMQ0 hM0 hT0 hr hCD hCD hCD hCD hCP hCP hDB
      hDN hDMQ hDT hDM hMDiff hBPoint hDB0
  have hInvM (θ : P) (hθ : θ ∈ V) : (M θ).IsInvertible := by
    change (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)).IsInvertible
    rw [commonSupport_negative_normal_multiplier_eq]
    exact hNormal θ hθ
  have hLeft : (fun θ => (M θ).comp (J θ)) =ᶠ[𝓝 x] R := by
    filter_upwards [hV.mem_nhds hx] with θ hθ
    exact commonSupport_lowRadial_first_remainder_left_identity a a1 ha ha1 S S1 hS hS1 hz hz1 c r θ hc (hInvM θ hθ)
  have hBound := norm_radial_taylor_derivative_of_left_identity M J R x r CP CD CP DR
    hM0 hJ0 hLeft (hInvM x hx) hr hr1 hCP hCD hCP hDR hMINorm hDM hJPoint hRNorm
  exact ⟨hJ0,hBound⟩

end ShrinkingSpheres
