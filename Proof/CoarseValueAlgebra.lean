import Proof.BoundaryGradientValues

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

theorem coarseValue_add (u v : SphereSobolev 0) (f g : UnitSphere → ℝ)
    (hu : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm u =ᵐ[sphereProbability] f)
    (hv : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm v =ᵐ[sphereProbability] g) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (u+v)
      =ᵐ[sphereProbability] fun w => f w+g w := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  rw [Z.symm.map_add]
  filter_upwards [Lp.coeFn_add (Z.symm u) (Z.symm v),hu,hv] with w hAdd hU hV
  exact hAdd.trans (congrArg₂ (fun a b : ℝ => a+b) hU hV)

theorem coarseValue_smul (c : ℝ) (u : SphereSobolev 0) (f : UnitSphere → ℝ)
    (hu : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm u =ᵐ[sphereProbability] f) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (c • u)
      =ᵐ[sphereProbability] fun w => c*f w := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  rw [Z.symm.map_smul]
  filter_upwards [Lp.coeFn_smul c (Z.symm u),hu] with w hScale hU
  exact hScale.trans (congrArg (fun a : ℝ => c*a) hU)

end ShrinkingSpheres
