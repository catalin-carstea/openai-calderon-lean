import Proof.SharpOrderOneMultiplier
import Proof.BoundaryCoefficientRepresentatives
import Proof.Archive.SphereCoefficientMultiplierCLM

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeOrderOneCoefficientMultiplierInverse
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

def coefficientThirdJet (F : SmoothCoefficientJets 2) : SmoothCoefficientJets 3 :=
  compactCoefficient 3 (coefficientValue 2 F) (contDiff_coefficientValue 2 F) (hasCompactSupport_coefficientValue 2 F)

lemma coefficientValue_coefficientThirdJet (F : SmoothCoefficientJets 2) :
    coefficientValue 3 (coefficientThirdJet F) = coefficientValue 2 F :=
  coefficientValue_compactCoefficient 3 _ _ _

/-- Canonical H1 realization of a supplied smooth coefficient. Its third jet
    only constructs the map; quantitative bounds use its local C1 data. -/
def oneBoundaryCoefficientMulL (F : SmoothCoefficientJets 2) : SphereSobolev 1 →L[ℝ] SphereSobolev 1 :=
  nativeOrderOneCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace (coefficientThirdJet F) F (coefficientValue_coefficientThirdJet F)

theorem oneBoundaryCoefficientMulL_coarse (F : SmoothCoefficientJets 2) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (oneBoundaryCoefficientMulL F u) =
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData F))
        (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  have h := sphereSobolevInclusionL_nativeOrderOneCoefficientMulL_zero fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (coefficientThirdJet F) F
      (coefficientValue_coefficientThirdJet F) u
  have hm : nativeH2CoefficientSmoothData (coefficientThirdJet F) = coefficientSmoothData F :=
    Subtype.ext (coefficientValue_coefficientThirdJet F)
  exact h.trans (congrArg (fun m : SmoothData =>
    coarseSphereScalarMulL (smoothSphereValue m) (sphereSobolevInclusionL 1 0 (by norm_num) u)) hm)

theorem norm_oneBoundaryCoefficientMulL_sphere_C1 (F : SmoothCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (hV : ∀ w : UnitSphere,|coefficientValue 2 F w.val| ≤ q)
    (hD : ∀ w : UnitSphere,‖fderiv ℝ (coefficientValue 2 F) w.val‖ ≤ q) :
    ‖oneBoundaryCoefficientMulL F‖ ≤ 73*q :=
  norm_orderOneMultiplier_local_C1 (coefficientSmoothData F) (oneBoundaryCoefficientMulL F)
    (oneBoundaryCoefficientMulL_coarse F) q hq hV hD

theorem LocalC1Bound.on_unitSphere {f : X → ℝ} {q : ℝ} (h : LocalC1Bound f q)
    (hf : ContDiff ℝ ∞ f) (w : UnitSphere) : |f w.val| ≤ q ∧ ‖fderiv ℝ f w.val‖ ≤ q := by
  have hc : IsClosed {x : X | |f x| ≤ q ∧ ‖fderiv ℝ f x‖ ≤ q} :=
    (isClosed_le hf.continuous.abs continuous_const).inter
      (isClosed_le (hf.continuous_fderiv (by simp)).norm continuous_const)
  have hsub : Metric.ball (0:X) 1 ⊆ {x : X | |f x| ≤ q ∧ ‖fderiv ℝ f x‖ ≤ q} := h
  apply closure_minimal hsub hc
  rw [closure_ball (0:X) (one_ne_zero : (1:ℝ) ≠ 0)]
  exact Metric.sphere_subset_closedBall w.property

theorem norm_oneBoundaryCoefficientMulL_local_C1 (F : SmoothCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (h : LocalC1Bound (coefficientValue 2 F) q) : ‖oneBoundaryCoefficientMulL F‖ ≤ 73*q :=
  norm_oneBoundaryCoefficientMulL_sphere_C1 F q hq
    (fun w => (h.on_unitSphere (contDiff_coefficientValue 2 F) w).1)
    (fun w => (h.on_unitSphere (contDiff_coefficientValue 2 F) w).2)

theorem oneBoundaryCoefficientMulL_congr_sphere (F G : SmoothCoefficientJets 2)
    (h : ∀ w : UnitSphere,coefficientValue 2 F w.val = coefficientValue 2 G w.val) :
    oneBoundaryCoefficientMulL F = oneBoundaryCoefficientMulL G := by
  have hm : smoothSphereValue (coefficientSmoothData F) = smoothSphereValue (coefficientSmoothData G) := by
    ext w
    exact h w
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 1 0 (by norm_num)
  exact (oneBoundaryCoefficientMulL_coarse F u).trans
    ((congrArg (fun q : C(UnitSphere,ℝ) => coarseSphereScalarMulL q
      (sphereSobolevInclusionL 1 0 (by norm_num) u)) hm).trans (oneBoundaryCoefficientMulL_coarse G u).symm)

theorem oneBoundaryCoefficientMulL_isInvertible_of_pos (F : SmoothCoefficientJets 2)
    (h : ∀ w : UnitSphere,0 < coefficientValue 2 F w.val) : (oneBoundaryCoefficientMulL F).IsInvertible := by
  apply nativeOrderOneCoefficientMulL_isInvertible_of_pos fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (coefficientThirdJet F) F
      (coefficientValue_coefficientThirdJet F)
  intro w
  exact (congrArg (fun z : ℝ => 0 < z) (congrFun (coefficientValue_coefficientThirdJet F) w.val)).mpr (h w)

end ShrinkingSpheres
