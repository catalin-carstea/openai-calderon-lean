import Proof.BoundaryAngularAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

/-- Radial response reconstructed from the same conormal operator and actual
    normal/tangential coefficients. -/
def conormalRadialL (F : SmoothCoefficientMatrix 2)
    (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))).inverse.comp
    (N-coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j))

/-- Its physical adjoint acts on H1 by the H1 normal reciprocal followed by
    the symmetric conormal operator and the exact tangential adjoint. -/
def conormalRadialAdjointL (F : SmoothCoefficientMatrix 2)
    (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (N-adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)).comp
    (oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse

theorem conormalRadialL_adjoint (F : SmoothCoefficientMatrix 2)
    (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hPos : ∀ w : UnitSphere,0 < (boundaryNormalCoefficientData F).1 w.val)
    (hN : ∀ u v,⟪N u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,N v⟫_ℝ)
    (u v : SphereSobolev 1) :
    ⟪conormalRadialL F N u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,conormalRadialAdjointL F N v⟫_ℝ := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let M := oneBoundaryCoefficientMulL (normalCoefficientJet F)
  let q := smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))
  let T := coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  let Td := adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  let w := M.inverse v
  have hP : ∀ z : UnitSphere,0 < coefficientValue 2 (normalCoefficientJet F) z.val := by
    intro z
    exact (congrArg (fun t : ℝ => 0 < t) (congrFun (coefficientValue_normalCoefficientJet F) z.val)).mpr (hPos z)
  have hM : (coarseSphereScalarMulL q).inverse (I0 v) = I0 w :=
    (oneBoundaryCoefficientMulL_inverse_coarse (normalCoefficientJet F) hP v).symm
  have hPair : ⟪N u-T u,I0 w⟫_ℝ = ⟪I0 u,N w-Td w⟫_ℝ :=
    (inner_sub_left _ _ _).trans ((congrArg₂ (fun a b : ℝ => a-b) (hN u w)
      (boundaryTangentialL_adjoint (fun j => tangentCoefficientJet F j) u w)).trans (inner_sub_right _ _ _).symm)
  exact (coarseSphereScalarMulL_inverse_symmetric q hP (N u-T u) (I0 v)).trans
    ((congrArg (fun z : SphereSobolev 0 => ⟪N u-T u,z⟫_ℝ) hM).trans hPair)

end ShrinkingSpheres
