import Proof.CommonSupportWeakPoissonRegularity
import Proof.ActualLowRadialEndpoint
import Proof.Archive.NativeBoundaryCoefficientFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 20
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma commonSupport_negative_normal_multiplier_eq
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p : P) :
    negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p) =
      negativeBoundaryCoefficientMulL (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p)) := by
  apply negativeBoundaryCoefficientMulL_congr_sphere
  intro w
  have hData := (coefficientSmoothData_normalCoefficientJetsFamily a ha S hS hz p).trans
    (coefficientSmoothData_normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p)).symm
  exact congrArg (fun f : SmoothData => f.1 w.val) hData

lemma commonSupport_negative_tangent_multiplier_eq
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (j : I) (p : P) :
    negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j p) =
      negativeBoundaryCoefficientMulL (tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j) := by
  apply negativeBoundaryCoefficientMulL_congr_sphere
  intro w
  have hData := (coefficientSmoothData_tangentCoefficientJetsFamily a ha S hS hz j p).trans
    (coefficientSmoothData_tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j).symm
  exact congrArg (fun f : SmoothData => f.1 w.val) hData

def commonSupportLowRadialErrorL (a : P × X → Mat) (ha : ContDiff ℝ ∞ a)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p : P) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  actualLowRadialErrorL (fun z => a (p,z)) (commonSupportEnergyMemLp a ha p)
    (commonSupportMatrixFamily 2 a ha S hS hz p)

/-- Genuine low radial response family, with the actual weak conormal solution
    and actual normal/tangent boundary coefficients. -/
theorem contDiffOn_commonSupportLowRadialErrorL
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (V : Set P)
    (hInv : ∀ p ∈ V,(commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (hNormal : ∀ p ∈ V,(negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))).IsInvertible) :
    ContDiffOn ℝ ∞ (commonSupportLowRadialErrorL a ha S hS hz) V := by
  let N := fun p => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p)
  let T := fun (j : I) p => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j p)
  have hN : ContDiff ℝ ∞ N := contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a ha S hS hz
  have hT (j : I) : ContDiff ℝ ∞ (T j) := contDiff_negativeHalf_tangentCoefficientFamily fixedSobolevCalculus
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a ha S hS hz j
  have hNInv : ∀ p ∈ V,(N p).IsInvertible := by
    intro p hp
    rw [show N p = negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p)) from
        commonSupport_negative_normal_multiplier_eq a ha S hS hz p]
    exact hNormal p hp
  have hNI := contDiffOn_banachInverseFamily N V hN.contDiffOn hNInv
  have hConormal := contDiffOn_commonSupportWeakConormalEndpoint a ha S hS hz V hInv
  have hInside : ContDiffOn ℝ ∞ (fun p => commonSupportWeakConormalEndpoint a ha p-
      (N p).comp fixedLowRadialL-∑ j : I,(T j p).comp (fixedSphereTangentialL j)) V :=
    (hConormal.sub (hN.contDiffOn.clm_comp contDiffOn_const)).sub
      (ContDiffOn.sum (fun j _ => (hT j).contDiffOn.clm_comp contDiffOn_const))
  have hResult := hNI.clm_comp hInside
  have hEq : commonSupportLowRadialErrorL a ha S hS hz = (fun p => (N p).inverse.comp
      (commonSupportWeakConormalEndpoint a ha p-(N p).comp fixedLowRadialL-
        ∑ j : I,(T j p).comp (fixedSphereTangentialL j))) := by
    funext p
    unfold commonSupportLowRadialErrorL actualLowRadialErrorL radialErrorAssembly
    have hNPoint := commonSupport_negative_normal_multiplier_eq a ha S hS hz p
    have hTPoint := fun j => commonSupport_negative_tangent_multiplier_eq a ha S hS hz j p
    simp only [N,T,hNPoint,hTPoint,commonSupportWeakConormalEndpoint]
  rw [hEq]
  exact hResult

end ShrinkingSpheres
