import Proof.BoundaryAngularAdjoint
import Proof.BoundaryCoefficientRepresentatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The normal component of an ambient boundary vector coefficient. -/
def vectorNormalData (F : I → SmoothCoefficientJets 2) : SmoothData :=
  ⟨fun x => ∑ j : I,x j*coefficientValue 2 (F j) x,
    ContDiff.sum (fun j _ => (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.mul
      (contDiff_coefficientValue 2 (F j)))⟩

lemma vectorNormalData_hasCompactSupport (F : I → SmoothCoefficientJets 2) :
    HasCompactSupport (vectorNormalData F).1 := by
  have hTerm (j : I) : HasCompactSupport (fun x : X => x j*coefficientValue 2 (F j) x) :=
    (hasCompactSupport_coefficientValue 2 (F j)).mul_left
  convert HasCompactSupport.finset_sum (s:=Finset.univ) (fun j _ => hTerm j) using 1
  funext x
  rfl

def vectorNormalJet (F : I → SmoothCoefficientJets 2) : SmoothCoefficientJets 2 :=
  compactCoefficient 2 (vectorNormalData F).1 (vectorNormalData F).2
    (vectorNormalData_hasCompactSupport F)

lemma coefficientValue_vectorNormalJet (F : I → SmoothCoefficientJets 2) :
    coefficientValue 2 (vectorNormalJet F) = (vectorNormalData F).1 :=
  coefficientValue_compactCoefficient 2 _ _ _

theorem vectorNormalJet_local_C1 (F : I → SmoothCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (hF : ∀ j,LocalC1Bound (coefficientValue 2 (F j)) q) :
    LocalC1Bound (coefficientValue 2 (vectorNormalJet F)) (6*q) := by
  rw [coefficientValue_vectorNormalJet]
  have hTerm (j : I) : LocalC1Bound (fun x : X => x j*coefficientValue 2 (F j) x) (2*q) := by
    simpa only [mul_one,PiLp.proj_apply] using localC1Bound_mul (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff
      (contDiff_coefficientValue 2 (F j)) (by norm_num : (0:ℝ) ≤ 1) hq
      (localC1Bound_coordinate j) (hF j)
  have hSum := localC1Bound_sum (fun j : I => fun x : X => x j*coefficientValue 2 (F j) x)
    (fun _ => 2*q) (fun j => (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.mul
      (contDiff_coefficientValue 2 (F j))) hTerm
  have hConst : (∑ _j : I,2*q) = 6*q := by simp only [Fin.sum_univ_three];ring
  rw [hConst] at hSum
  exact hSum

/-- Boundary action of a vector coefficient on a harmonic extension, split into
    tangential rotations and its true radial response. -/
def boundaryGradientL (F : I → SmoothCoefficientJets 2)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  coarseBoundaryTangentialL F+
    (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet F)))).comp D

def boundaryGradientAdjointL (F : I → SmoothCoefficientJets 2)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  adjointBoundaryTangentialL F+Da.comp (oneBoundaryCoefficientMulL (vectorNormalJet F))

/-- Exact physical L2 adjunction for the full boundary gradient action. -/
theorem boundaryGradientL_adjoint (F : I → SmoothCoefficientJets 2)
    (D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hD : ∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ)
    (u v : SphereSobolev 1) :
    ⟪boundaryGradientL F D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,boundaryGradientAdjointL F Da v⟫_ℝ := by
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let M := oneBoundaryCoefficientMulL (vectorNormalJet F)
  have hNormal : ⟪coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet F)))
      (D u),I0 v⟫_ℝ = ⟪I0 u,Da (M v)⟫_ℝ :=
    (coarseSphereScalarMulL_symmetric _ _ _).trans
      ((congrArg (fun z : SphereSobolev 0 => ⟪D u,z⟫_ℝ)
        (oneBoundaryCoefficientMulL_coarse (vectorNormalJet F) v)).symm.trans (hD u (M v)))
  change ⟪coarseBoundaryTangentialL F u+_,I0 v⟫_ℝ = ⟪I0 u,adjointBoundaryTangentialL F v+_⟫_ℝ
  rw [inner_add_left,inner_add_right]
  exact congrArg₂ (fun a b : ℝ => a+b) (boundaryTangentialL_adjoint F u v) hNormal

/-- A common C1 bound on the vector coefficients controls the physical adjoint
    on H1, with no higher coefficient jets in the norm estimate. -/
theorem norm_boundaryGradientAdjointL_local_C1 (F : I → SmoothCoefficientJets 2)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (q : ℝ) (hq : 0 ≤ q)
    (hF : ∀ j,LocalC1Bound (coefficientValue 2 (F j)) q) :
    ‖boundaryGradientAdjointL F Da‖ ≤
      (73*boundaryTangentialAdjointBudget+438*‖Da‖)*q := by
  have hEach (j : I) : ‖oneBoundaryCoefficientMulL (F j)‖ ≤ 73*q :=
    norm_oneBoundaryCoefficientMulL_local_C1 (F j) q hq (hF j)
  have hNormal : ‖oneBoundaryCoefficientMulL (vectorNormalJet F)‖ ≤ 73*(6*q) :=
    norm_oneBoundaryCoefficientMulL_local_C1 (vectorNormalJet F) (6*q) (by positivity)
      (vectorNormalJet_local_C1 F q hq hF)
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_adjointBoundaryTangentialL_le F (73*q) (by positivity) hEach)
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left hNormal (norm_nonneg Da)))).trans_eq (by ring))

end ShrinkingSpheres
