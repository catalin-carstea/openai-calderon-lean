import Proof.PhysicalMovingBoundaryAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothAngularCasimir
open OAI.AnisotropicCalderon.NativeH2ThreeHalfValueTrace
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier

/-- Canonical high Sobolev boundary datum of a globally smooth ambient scalar
    function, obtained from its genuine H2 value trace. -/
def smoothHighBoundaryData (f : SmoothData) : SphereSobolev (3/2:ℝ) :=
  nativeThreeHalfValueTraceL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics fixedUnitBallValueTrace (smoothBallSobolev 2 f)

def smoothOneBoundaryData (f : SmoothData) : SphereSobolev 1 :=
  sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (smoothHighBoundaryData f)

theorem smoothHighBoundaryData_coarse (f : SmoothData) :
    sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (smoothHighBoundaryData f) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (smoothSphereLift f.1 f.2) := by
  have h := sphereSobolevInclusionL_nativeThreeHalfValueTraceL_zero fixedSobolevCalculus
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (smoothBallSobolev 2 f)
  rw [firstOrder_smoothBallSobolev,fixedUnitBallValueTrace.valueTrace_smooth] at h
  exact h

theorem smoothOneBoundaryData_coarse (f : SmoothData) :
    sphereSobolevInclusionL 1 0 (by norm_num) (smoothOneBoundaryData f) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (smoothSphereLift f.1 f.2) :=
  (congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => I (smoothHighBoundaryData f))
    (sphereSobolevInclusionL_trans (3/2:ℝ) 1 0 (by norm_num) (by norm_num))).trans
      (smoothHighBoundaryData_coarse f)

theorem smoothHighBoundaryData_value (f : SmoothData) :
    fixedBoundaryValueL (smoothHighBoundaryData f) = smoothSphereLift f.1 f.2 := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  exact (congrArg Z.symm (smoothHighBoundaryData_coarse f)).trans (Z.symm_apply_apply _)

theorem smoothHighBoundaryData_value_ae (f : SmoothData) :
    fixedBoundaryValueL (smoothHighBoundaryData f) =ᵐ[sphereProbability] fun w : UnitSphere => f.1 w.val := by
  rw [smoothHighBoundaryData_value]
  exact ContinuousMap.coeFn_toLp (p:=2) (μ:=sphereProbability) (𝕜:=ℝ) (smoothSphereValue f)

theorem smoothOneBoundaryData_value_ae (f : SmoothData) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) (smoothOneBoundaryData f))
        =ᵐ[sphereProbability] fun w : UnitSphere => f.1 w.val := by
  rw [smoothOneBoundaryData_coarse,LinearIsometryEquiv.symm_apply_apply]
  exact ContinuousMap.coeFn_toLp (p:=2) (μ:=sphereProbability) (𝕜:=ℝ) (smoothSphereValue f)

theorem smoothHighBoundaryData_congr_sphere (f g : SmoothData)
    (h : ∀ w : UnitSphere,f.1 w.val = g.1 w.val) : smoothHighBoundaryData f = smoothHighBoundaryData g := by
  apply sphereSobolevInclusionL_injective (3/2:ℝ) 0 (by norm_num)
  rw [smoothHighBoundaryData_coarse,smoothHighBoundaryData_coarse]
  have hValue : smoothSphereValue f = smoothSphereValue g := ContinuousMap.ext h
  exact congrArg (fun v : SphereL2 => sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics v)
    (congrArg (ContinuousMap.toLp 2 sphereProbability ℝ) hValue)

end ShrinkingSpheres
