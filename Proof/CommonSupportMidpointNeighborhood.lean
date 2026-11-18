import Proof.CoerciveNeighborhood
import Proof.CommonSupportMidpointRadialRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
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
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The actual weak, strong and normal inverse loci have one open common
    neighborhood around any valid coefficient parameter, in any finite
    dimensional parameter space. The true midpoint family is smooth there. -/
theorem exists_commonSupport_midpoint_neighborhood
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p0 : P) (V0 : Set P) (hV0 : IsOpen V0) (hp0 : p0 ∈ V0)
    (hCoercive0 : IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha p0)))
    (hStrong0 : (strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha S hS hz p0)).IsInvertible)
    (hNormal0 : (negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p0))).IsInvertible) :
    ∃ V : Set P,IsOpen V ∧ p0 ∈ V ∧ V ⊆ V0 ∧
      (∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha p))) ∧
      (∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible) ∧
      (∀ p ∈ V,(negativeBoundaryCoefficientMulL
        (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))).IsInvertible) ∧
      ∃ R : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0,ContDiffOn ℝ ∞ R V ∧
        ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 a ha S hS hz p)) := by
  let B := commonSupportZeroWeakEnergy a ha
  let D := fun p => strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)
  let M := fun p => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p)
  have hBSmooth : ContDiff ℝ ∞ B := contDiff_commonSupportZeroWeakEnergy a ha S hS hz
  have hDSmooth : ContDiff ℝ ∞ D := contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha S hS hz
  have hMSmooth : ContDiff ℝ ∞ M := contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a ha S hS hz
  let V := V0 ∩ {p : P | IsCoercive (B p)} ∩ {p : P | (D p).IsInvertible} ∩ {p : P | (M p).IsInvertible}
  have hV : IsOpen V := ((hV0.inter ((isOpen_setOf_isCoercive (E:=BallH1Zero)).preimage hBSmooth.continuous)).inter
    (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hDSmooth.continuous)).inter
      (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hMSmooth.continuous)
  have hNorm0 : (M p0).IsInvertible := by
    change (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p0)).IsInvertible
    rw [commonSupport_negative_normal_multiplier_eq]
    exact hNormal0
  have hHere : p0 ∈ V := ⟨⟨⟨hp0,hCoercive0⟩,hStrong0⟩,hNorm0⟩
  have hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha p)) :=
    fun p hp => hp.1.1.2
  have hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible := fun p hp => hp.1.2
  have hNormal : ∀ p ∈ V,(negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))).IsInvertible := by
    intro p hp
    rw [← commonSupport_negative_normal_multiplier_eq]
    exact hp.2
  obtain ⟨R,hR,hRestrict⟩ := exists_commonSupport_smooth_midpoint_radial_family a ha S hS hz V hV hCoercive hStrong hNormal
  exact ⟨V,hV,hHere,fun p hp => hp.1.1.1,hCoercive,hStrong,hNormal,R,hR,hRestrict⟩

end ShrinkingSpheres
