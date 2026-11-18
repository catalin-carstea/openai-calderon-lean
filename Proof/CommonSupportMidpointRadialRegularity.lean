import Proof.CommonSupportLowRadialRegularity
import Proof.CommonSupportPoissonRegularity
import Proof.Archive.SphereSobolevCompatibleInterpolationTopology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Any genuine common-support coefficient family with coercive weak and
    invertible strong/normal maps has one smooth compatible midpoint radial
    error family. This also applies to rotated parameter families. -/
theorem exists_commonSupport_smooth_midpoint_radial_family
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (V : Set P) (hV : IsOpen V)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha p)))
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible)
    (hNormal : ∀ p ∈ V,(negativeBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))).IsInvertible) :
    ∃ R : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0,ContDiffOn ℝ ∞ R V ∧
      ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
          (actualHighRadialErrorL (commonSupportMatrixFamily 2 a ha S hS hz p)) := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  have hWeak (p : P) (hp : p ∈ V) : (commonSupportZeroWeakEnergy a ha p).IsInvertible :=
    isInvertible_of_bilinear_coercive _ (hCoercive p hp)
  let T : P → SphereSobolevEndpointPair := fun p =>
    (commonSupportLowRadialErrorL a ha S hS hz p,actualHighRadialErrorL (F p))
  have hCompatible (p : P) (hp : p ∈ V) : T p ∈ sphereSobolevCompatibleEndpoints := by
    have hPoint (z : X) (hzBall : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F p) z = a (p,z) := by
      simp only [F,coefficientMatrixField_commonSupportMatrixFamily]
    have hCompat := actual_radial_endpoints_compatible (commonSupportEnergyMemLp a ha p)
      (hCoercive p hp) (F p) hPoint (hStrong p hp) (hNormal p hp)
    have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
      (by norm_num) (by norm_num) (by ring)
    exact (congrArg (fun J : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      J.comp (actualHighRadialErrorL (F p))) hI).trans hCompat
  have hSmoothT : ContDiffOn ℝ ∞ T V :=
    (contDiffOn_commonSupportLowRadialErrorL a ha S hS hz V hWeak hNormal).prodMk
      (contDiffOn_commonSupport_highRadialErrorL a ha S hS hz V hStrong)
  let R := sphereSobolevCompatibleInterpolationFamily T V hCompatible
  refine ⟨R,contDiffOn_sphereSobolevCompatibleInterpolationFamily T V hV hCompatible hSmoothT,?_⟩
  intro p hp
  rw [show R p = sphereSobolevMidpointL (T p).1 (T p).2 (hCompatible p hp) from
    sphereSobolevCompatibleInterpolationFamily_of_mem T V hCompatible p hp]
  exact sphereSobolevMidpointL_inclusion (T p).1 (T p).2 (hCompatible p hp)

end ShrinkingSpheres
